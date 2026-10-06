// ==UserScript==
// @name         智能导航预取器 - 稳定重构版
// @namespace    https://github.com/network-optimized
// @version      4.2.2
// @description  基于 v4.0 稳定核心的性能增强版：保持原有 CSP/Cloudflare 兼容路径，仅优化用户意图响应、视口范围和队列节奏
// @license      MIT
// @match        http://*/*
// @match        https://*/*
// @noframes
// @run-at       document-start
// @grant        none
// ==/UserScript==

(() => {
    'use strict';

    const 配置 = Object.freeze({
        // 安全优先：默认只预取当前 origin 下的页面。
        仅同源: true,

        // 鼠标停留超过该时间才认为“可能要点”，避免划过菜单时产生大量误预取。
        悬停触发延迟: 45,

        // 当前页面 load 之后再启动视口预测，避免抢首屏资源。
        视口预测启动延迟: 600,
        视口扩展范围: '1000px 0px',

        // 5 分钟内不重复提示同一 URL。
        记录有效期: 5 * 60 * 1000,

        // 防止无限滚动网站疯狂预取。
        单周期最大预取数: 32,
        单周期最大视口预取数: 12,
        最大观察链接数: 3000,

        // 高意图（hover/focus/touch/pointerdown）更快，视口预测继续节流。
        // 仍由浏览器决定真正的 HTTP/2 / HTTP/3 网络并发。
        高优先提示最小间隔: 30,
        低优先提示最小间隔: 90,

        // 支持时优先使用 Speculation Rules；不支持时回退 rel=prefetch。
        优先推测规则: true,

        // 省流量/2G 网络下停止主动预取。
        尊重省流模式: true,

        // 调试时改成 true，可在控制台观察工作情况。
        调试日志: false,
    });

    // 这些 URL 即使是 GET，也可能具有状态改变或账号操作副作用，因此默认不碰。
    const 危险动作关键词 =
        /(?:^|[\/?&#=_-])(?:logout|logoff|signout|sign-off|delete|remove|destroy|unsubscribe|checkout|purchase|payment|pay|confirm|submit|revoke|disable)(?:$|[\/?&#=_-])/i;

    // 明显不是网页导航的资源直接排除。
    const 非页面扩展名 =
        /\.(?:zip|rar|7z|tar|gz|bz2|xz|pdf|docx?|xlsx?|pptx?|exe|msi|dmg|iso|apk|mp4|mkv|avi|mov|webm|mp3|flac|wav|jpg|jpeg|png|gif|webp|avif|svg|ico|css|js|mjs|json|xml|wasm)(?:$|[?#])/i;

    // url -> { time, source, node, backend }
    const 已提示 = new Map();

    // url -> source
    const 已排队 = new Map();

    const 高优先队列 = [];
    const 低优先队列 = [];

    const 悬停计时器 = new WeakMap();
    const 已观察链接 = new WeakSet();

    let 正在处理队列 = false;
    let 上次提示时间 = 0;

    let 视口观察器 = null;
    let DOM观察器 = null;

    let 已观察数量 = 0;
    let 推测规则被CSP禁用 = false;

    const 支持推测规则 = Boolean(
        配置.优先推测规则 &&
        HTMLScriptElement.supports &&
        HTMLScriptElement.supports('speculationrules')
    );

    function 日志(...args) {
        if (配置.调试日志) {
            console.debug('[智能导航预取器]', ...args);
        }
    }

    /**
     * 不再尝试所谓“实时千兆测速”。
     *
     * navigator.connection 只用来判断：
     * 1. 是否开启 saveData；
     * 2. 是否处于 2G / slow-2g。
     *
     * 真正的 HTTP/2 / HTTP/3 并发交给浏览器自己调度。
     */
    function 当前网络允许预取() {
        if (!配置.尊重省流模式) {
            return true;
        }

        const connection =
            navigator.connection ||
            navigator.mozConnection ||
            navigator.webkitConnection;

        if (!connection) {
            return true;
        }

        if (connection.saveData) {
            return false;
        }

        const type = String(
            connection.effectiveType || ''
        ).toLowerCase();

        return type !== 'slow-2g' && type !== '2g';
    }

    /**
     * 检查一个 <a> 是否适合被提前预取。
     */
    function 规范化URL(anchor) {
        if (!(anchor instanceof HTMLAnchorElement)) {
            return null;
        }

        if (!anchor.hasAttribute('href')) {
            return null;
        }

        if (anchor.hasAttribute('download')) {
            return null;
        }

        // 网站或用户可以主动标记某些链接禁止预取。
        if (
            anchor.matches(
                '[data-no-prefetch], .no-prefetch'
            )
        ) {
            return null;
        }

        const raw =
            (anchor.getAttribute('href') || '').trim();

        if (!raw || raw.startsWith('#')) {
            return null;
        }

        let url;

        try {
            url = new URL(
                anchor.href,
                location.href
            );
        } catch {
            return null;
        }

        // 只允许真正的网页协议。
        if (
            url.protocol !== 'http:' &&
            url.protocol !== 'https:'
        ) {
            return null;
        }

        // 避免包含用户名密码的 URL。
        if (url.username || url.password) {
            return null;
        }

        // 默认禁止跨源预取。
        if (
            配置.仅同源 &&
            url.origin !== location.origin
        ) {
            return null;
        }

        // hash 不影响服务器返回的 HTML，
        // 去掉之后可以正确去重。
        url.hash = '';

        const current =
            new URL(location.href);

        current.hash = '';

        // 不重新预取当前页面。
        if (url.href === current.href) {
            return null;
        }

        const pathAndQuery =
            url.pathname + url.search;

        if (
            非页面扩展名.test(
                pathAndQuery
            )
        ) {
            return null;
        }

        if (
            危险动作关键词.test(
                pathAndQuery
            )
        ) {
            return null;
        }

        return url.href;
    }

    /**
     * 清理超过 TTL 的记录。
     */
    function 清理过期记录() {
        const now = Date.now();

        for (
            const [url, record]
            of 已提示
        ) {
            if (
                now - record.time <
                配置.记录有效期
            ) {
                continue;
            }

            // 仅删除本脚本插入的 DOM 节点。
            // 浏览器内部缓存仍由浏览器自己决定何时淘汰。
            if (
                record.node?.isConnected
            ) {
                record.node.remove();
            }

            已提示.delete(url);
        }
    }

    /**
     * 已完成 + 正在排队的视口预取数量。
     */
    function 当前视口提示数() {
        let count = 0;

        for (
            const record
            of 已提示.values()
        ) {
            if (
                record.source ===
                'viewport'
            ) {
                count++;
            }
        }

        for (
            const source
            of 已排队.values()
        ) {
            if (
                source === 'viewport'
            ) {
                count++;
            }
        }

        return count;
    }

    /**
     * 用户明确悬停/点击时，
     * 可以牺牲一个低价值视口预测名额。
     */
    function 为高优先释放名额() {
        // 优先取消尚未发出的低优先任务。
        const queued =
            低优先队列.pop();

        if (queued) {
            已排队.delete(
                queued.url
            );

            return true;
        }

        // 如果没有待执行低优先任务，
        // 再释放最老的视口预取记录。
        let oldestUrl = null;
        let oldestTime = Infinity;

        for (
            const [url, record]
            of 已提示
        ) {
            if (
                record.source !==
                'viewport'
            ) {
                continue;
            }

            if (
                record.time <
                oldestTime
            ) {
                oldestTime =
                    record.time;

                oldestUrl = url;
            }
        }

        if (!oldestUrl) {
            return false;
        }

        const record =
            已提示.get(
                oldestUrl
            );

        record?.node?.remove();

        已提示.delete(
            oldestUrl
        );

        return true;
    }

    /**
     * 判断 URL 当前是否还能加入预取队列。
     */
    function 可以加入提示(
        url,
        source
    ) {
        清理过期记录();

        if (!当前网络允许预取()) {
            return false;
        }

        if (
            已提示.has(url) ||
            已排队.has(url)
        ) {
            return false;
        }

        // 视口预测严格限制数量。
        if (
            source === 'viewport' &&
            当前视口提示数() >=
                配置.单周期最大视口预取数
        ) {
            return false;
        }

        // 总量达到上限。
        if (
            已提示.size +
                已排队.size >=
            配置.单周期最大预取数
        ) {
            // 用户明确意图可以挤掉低价值视口预测。
            if (
                source !== 'intent' ||
                !为高优先释放名额()
            ) {
                return false;
            }
        }

        return true;
    }

    /**
     * 加入高/低优先队列。
     */
    function 加入提示队列(
        url,
        priority,
        source
    ) {
        if (
            !可以加入提示(
                url,
                source
            )
        ) {
            return;
        }

        const item = {
            url,
            source,
        };

        已排队.set(
            url,
            source
        );

        if (
            priority === 'high'
        ) {
            高优先队列.push(
                item
            );
        } else {
            低优先队列.push(
                item
            );
        }

        处理队列();
    }

    /**
     * Chrome / Edge：
     * 使用 Speculation Rules prefetch。
     */
    function 插入推测规则(url) {
        const script =
            document.createElement(
                'script'
            );

        script.type =
            'speculationrules';

        script.textContent =
            JSON.stringify({
                prefetch: [
                    {
                        source: 'list',
                        urls: [url],
                    },
                ],
            });

        (
            document.head ||
            document.documentElement
        ).appendChild(script);

        return script;
    }

    /**
     * Firefox / Safari / CSP fallback：
     * 使用传统 rel=prefetch。
     */
    function 插入Prefetch(url) {
        const link =
            document.createElement(
                'link'
            );

        link.rel = 'prefetch';
        link.href = url;

        (
            document.head ||
            document.documentElement
        ).appendChild(link);

        return link;
    }

    /**
     * 真正向浏览器提交一个导航预测。
     */
    function 执行提示(item) {
        const {
            url,
            source,
        } = item;

        已排队.delete(url);

        if (
            !可以加入提示(
                url,
                source
            )
        ) {
            return;
        }

        let node;
        let backend;

        const 使用推测规则 =
            支持推测规则 &&
            !推测规则被CSP禁用;

        try {
            node =
                使用推测规则
                    ? 插入推测规则(url)
                    : 插入Prefetch(url);

            backend =
                使用推测规则
                    ? 'speculation'
                    : 'prefetch';
        } catch (error) {
            日志(
                '插入预取提示失败:',
                url,
                error
            );

            return;
        }

        已提示.set(
            url,
            {
                time: Date.now(),
                source,
                node,
                backend,
            }
        );

        日志(
            backend === 'speculation'
                ? 'Speculation Rules prefetch:'
                : 'link prefetch:',
            url,
            source
        );
    }

    /**
     * 高优先永远先于低优先。
     *
     * 不人为控制 TCP/HTTP 连接数量，
     * 只控制“提示浏览器”的节奏。
     */
    function 处理队列() {
        if (正在处理队列) {
            return;
        }

        正在处理队列 = true;

        const step = () => {
            let item =
                高优先队列.shift();

            if (!item) {
                // 后台标签页不执行低优先视口预取。
                if (
                    document.visibilityState ===
                    'visible'
                ) {
                    item =
                        低优先队列.shift();
                }
            }

            if (!item) {
                正在处理队列 =
                    false;

                return;
            }

            const now =
                performance.now();

            const interval =
                item.source === 'intent'
                    ? 配置.高优先提示最小间隔
                    : 配置.低优先提示最小间隔;

            const wait =
                Math.max(
                    0,
                    interval -
                        (
                            now -
                            上次提示时间
                        )
                );

            setTimeout(
                () => {
                    执行提示(item);

                    上次提示时间 =
                        performance.now();

                    step();
                },
                wait
            );
        };

        step();
    }

    /**
     * 高概率导航：
     * hover / focus / touch / pointerdown。
     */
    function 为链接安排高优先预取(
        anchor
    ) {
        const url =
            规范化URL(anchor);

        if (url) {
            加入提示队列(
                url,
                'high',
                'intent'
            );
        }
    }

    /**
     * 严格 CSP 可能拒绝：
     *
     * <script type="speculationrules">
     *
     * 一旦检测到 inline script-src 阻止，
     * 后续直接使用 link rel=prefetch。
     */
    document.addEventListener(
        'securitypolicyviolation',
        event => {
            if (
                !支持推测规则 ||
                推测规则被CSP禁用
            ) {
                return;
            }

            const directive =
                String(
                    event.effectiveDirective ||
                    ''
                );

            const blockedInline =
                event.blockedURI ===
                    'inline' ||
                event.blockedURI === '';

            const scriptDirective =
                directive ===
                    'script-src' ||
                directive ===
                    'script-src-elem';

            if (
                !blockedInline ||
                !scriptDirective
            ) {
                return;
            }

            推测规则被CSP禁用 =
                true;

            const now =
                Date.now();

            // 将刚刚可能被 CSP 拒绝的预取重新补发。
            for (
                const [url, record]
                of 已提示
            ) {
                if (
                    record.backend !==
                    'speculation'
                ) {
                    continue;
                }

                if (
                    now -
                        record.time >
                    1500
                ) {
                    continue;
                }

                try {
                    record.node?.remove();

                    record.node =
                        插入Prefetch(
                            url
                        );

                    record.backend =
                        'prefetch';

                    record.time =
                        now;

                    日志(
                        'CSP 阻止 speculationrules，已回退 prefetch:',
                        url
                    );
                } catch (error) {
                    日志(
                        'CSP 回退 prefetch 失败:',
                        url,
                        error
                    );
                }
            }
        },
        true
    );

    // ============================================================
    // 用户意图预测
    // ============================================================

    /**
     * pointerover 可以冒泡，
     * 因此整个网页只需要一个监听器。
     *
     * 原脚本是每个 <a> 单独 addEventListener，
     * 大型网页会产生大量监听器。
     */
    document.addEventListener(
        'pointerover',
        event => {
            const anchor =
                event.target.closest?.(
                    'a[href]'
                );

            if (!anchor) {
                return;
            }

            // 在同一个 a 的子节点之间移动，
            // 不重新触发。
            if (
                event.relatedTarget &&
                anchor.contains(
                    event.relatedTarget
                )
            ) {
                return;
            }

            if (
                悬停计时器.has(
                    anchor
                )
            ) {
                return;
            }

            const timer =
                setTimeout(
                    () => {
                        悬停计时器.delete(
                            anchor
                        );

                        为链接安排高优先预取(
                            anchor
                        );
                    },
                    配置.悬停触发延迟
                );

            悬停计时器.set(
                anchor,
                timer
            );
        },
        true
    );

    /**
     * 鼠标在 45 ms 内离开：
     * 认为只是划过，不浪费流量。
     */
    document.addEventListener(
        'pointerout',
        event => {
            const anchor =
                event.target.closest?.(
                    'a[href]'
                );

            if (!anchor) {
                return;
            }

            if (
                event.relatedTarget &&
                anchor.contains(
                    event.relatedTarget
                )
            ) {
                return;
            }

            const timer =
                悬停计时器.get(
                    anchor
                );

            if (timer) {
                clearTimeout(timer);

                悬停计时器.delete(
                    anchor
                );
            }
        },
        true
    );

    /**
     * 键盘 Tab 到一个链接：
     * 认为用户有较强导航意图。
     */
    document.addEventListener(
        'focusin',
        event => {
            const anchor =
                event.target.closest?.(
                    'a[href]'
                );

            if (anchor) {
                为链接安排高优先预取(
                    anchor
                );
            }
        },
        true
    );

    /**
     * 鼠标/触控已经按下：
     * 用户几乎确定要进入这个页面。
     */
    document.addEventListener(
        'pointerdown',
        event => {
            const anchor =
                event.target.closest?.(
                    'a[href]'
                );

            if (anchor) {
                为链接安排高优先预取(
                    anchor
                );
            }
        },
        {
            capture: true,
            passive: true,
        }
    );

    /**
     * 某些触屏环境没有完整 PointerEvent 行为，
     * 因此保留 touchstart 作为补充。
     */
    document.addEventListener(
        'touchstart',
        event => {
            const anchor =
                event.target.closest?.(
                    'a[href]'
                );

            if (anchor) {
                为链接安排高优先预取(
                    anchor
                );
            }
        },
        {
            capture: true,
            passive: true,
        }
    );

    // ============================================================
    // 低优先级视口预测
    // ============================================================

    function 观察链接(anchor) {
        if (
            !(
                anchor instanceof
                HTMLAnchorElement
            )
        ) {
            return;
        }

        if (
            已观察链接.has(
                anchor
            )
        ) {
            return;
        }

        if (
            已观察数量 >=
            配置.最大观察链接数
        ) {
            return;
        }

        // 先过滤无效链接，
        // 减少 IntersectionObserver 压力。
        if (
            !规范化URL(
                anchor
            )
        ) {
            return;
        }

        已观察链接.add(
            anchor
        );

        已观察数量++;

        视口观察器.observe(
            anchor
        );
    }

    function 取消观察链接(
        anchor
    ) {
        if (
            !(
                anchor instanceof
                HTMLAnchorElement
            )
        ) {
            return;
        }

        if (
            !已观察链接.has(
                anchor
            )
        ) {
            return;
        }

        视口观察器.unobserve(
            anchor
        );

        已观察链接.delete(
            anchor
        );

        已观察数量 =
            Math.max(
                0,
                已观察数量 - 1
            );
    }

    /**
     * MutationObserver 新增节点可能本身就是 <a>，
     * 所以必须同时检查：
     *
     * node.matches('a')
     *
     * 和：
     *
     * node.querySelectorAll('a')
     *
     * 这正是原脚本漏掉的地方。
     */
    function 扫描节点中的链接(
        node,
        action
    ) {
        if (
            !(node instanceof Element)
        ) {
            return;
        }

        if (
            node.matches('a[href]')
        ) {
            action(node);
        }

        node.querySelectorAll?.(
            'a[href]'
        ).forEach(
            action
        );
    }

    function 启动视口预测() {
        if (
            !(
                'IntersectionObserver'
                in window
            )
        ) {
            return;
        }

        视口观察器 =
            new IntersectionObserver(
                entries => {
                    for (
                        const entry
                        of entries
                    ) {
                        if (
                            !entry.isIntersecting
                        ) {
                            continue;
                        }

                        const anchor =
                            entry.target;

                        // 当前 DOM 链接只需要触发一次。
                        取消观察链接(
                            anchor
                        );

                        const url =
                            规范化URL(
                                anchor
                            );

                        if (url) {
                            加入提示队列(
                                url,
                                'low',
                                'viewport'
                            );
                        }
                    }
                },
                {
                    root: null,

                    rootMargin:
                        配置.视口扩展范围,

                    threshold: 0.01,
                }
            );

        /**
         * 页面 load 完成之后完整扫描一次，
         * 不再依赖 document-start 时的 MutationObserver
         * 去“猜”HTML parser 加进来的链接。
         */
        document
            .querySelectorAll(
                'a[href]'
            )
            .forEach(
                观察链接
            );

        /**
         * 页面完成后再监听动态 DOM，
         * 兼容 React / Vue / SPA / 无限滚动。
         */
        DOM观察器 =
            new MutationObserver(
                records => {
                    for (
                        const record
                        of records
                    ) {
                        if (
                            record.type ===
                            'childList'
                        ) {
                            record
                                .addedNodes
                                .forEach(
                                    node =>
                                        扫描节点中的链接(
                                            node,
                                            观察链接
                                        )
                                );

                            record
                                .removedNodes
                                .forEach(
                                    node =>
                                        扫描节点中的链接(
                                            node,
                                            取消观察链接
                                        )
                                );
                        } else if (
                            record.type ===
                                'attributes' &&
                            record.target
                                instanceof
                                HTMLAnchorElement
                        ) {
                            /**
                             * SPA 经常保留同一个 <a>
                             * 但修改 href。
                             */
                            取消观察链接(
                                record.target
                            );

                            观察链接(
                                record.target
                            );
                        }
                    }
                }
            );

        DOM观察器.observe(
            document.documentElement,
            {
                childList: true,
                subtree: true,

                attributes: true,

                attributeFilter: [
                    'href',
                    'download',
                ],
            }
        );

        日志(
            '视口预测已启动'
        );
    }

    /**
     * 当前页面优先。
     *
     * load 后再等 600 ms，
     * 才开始主动观察并预取附近页面。
     */
    function 延迟启动视口预测() {
        setTimeout(
            启动视口预测,
            配置.视口预测启动延迟
        );
    }

    if (
        document.readyState ===
        'complete'
    ) {
        延迟启动视口预测();
    } else {
        window.addEventListener(
            'load',
            延迟启动视口预测,
            {
                once: true,
            }
        );
    }

    /**
     * 网络由 2G / Save Data 恢复后，
     * 尝试继续处理队列。
     */
    const connection =
        navigator.connection ||
        navigator.mozConnection ||
        navigator.webkitConnection;

    connection?.addEventListener?.(
        'change',
        () => {
            if (
                当前网络允许预取()
            ) {
                处理队列();
            }
        }
    );

    /**
     * 标签页重新回到前台后，
     * 继续低优先队列。
     */
    document.addEventListener(
        'visibilitychange',
        () => {
            if (
                document.visibilityState ===
                'visible'
            ) {
                处理队列();
            }
        }
    );

    日志(
        '初始化完成',
        {
            backend:
                支持推测规则
                    ? 'Speculation Rules（遇 CSP 自动回退）'
                    : 'link rel=prefetch',
        }
    );
})();
