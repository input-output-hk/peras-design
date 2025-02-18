import { themes as prismThemes } from 'prism-react-renderer';
import type { Config } from '@docusaurus/types';
import type * as Preset from '@docusaurus/preset-classic';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';

const config: Config = {
    title: 'Ouroboros Peras',
    tagline: 'Faster settlement on Cardano',
    favicon: 'img/pilcrow.ico',

    url: 'https://peras.cardano-scaling.org/',
    baseUrl: '/',

    onBrokenLinks: 'throw',
    onBrokenMarkdownLinks: 'warn',

    // Even if you don't use internationalization, you can use this field to set
    // useful metadata like html lang. For example, if your site is Chinese, you
    // may want to replace "en" with "zh-Hans".
    i18n: {
        defaultLocale: 'en',
        locales: ['en'],
    },

    scripts: [
        {
            src: "https://plausible.io/js/script.js",
            defer: true,
            "data-domain": "peras.cardano-scaling.org",
        },
    ],

    presets: [
        [
            'classic',
            {
                docs: {
                    sidebarPath: './sidebars.ts',
                    // Please change this to your repo.
                    // Remove this to remove the "edit this page" links.
                    editUrl: 'https://github.com/facebook/docusaurus/tree/main/packages/create-docusaurus/templates/shared/',
                    remarkPlugins: [remarkMath],
                    rehypePlugins: [rehypeKatex],

                },
                blog: {
                    path: "weekly",
                    routeBasePath: "/weekly",
                    showReadingTime: true,
                    blogTitle: 'Peras R&D Updates',
                    blogDescription: 'Regular updates from Peras R&D Team',
                    postsPerPage: 5,
                    blogSidebarTitle: 'Recent Posts',
                    blogSidebarCount: 10,
                    feedOptions: {
                        type: 'all',
                        title: 'Peras R&D Feed',
                        description: 'Regular updates from Peras R&D Teams',
                    },
                }
                ,
                theme: {
                    customCss: './src/css/custom.css',
                },
            } satisfies Preset.Options,
        ],
    ],
    stylesheets: [
        {
            href: 'https://cdn.jsdelivr.net/npm/katex@0.13.24/dist/katex.min.css',
            type: 'text/css',
            integrity:
                'sha384-odtC+0UGzzFL/6PNoE8rX/SPcQDXBJ+uRepguP4QkPCm2LBxH3FA3y+fKSiJ+AmM',
            crossorigin: 'anonymous',
        },
    ],
    themeConfig: {
        tableOfContents: {
            minHeadingLevel: 2,
            maxHeadingLevel: 3,
        },
        navbar: {
            title: 'Peras R&D',
            logo: {
                alt: 'Peras Logo',
                src: 'img/logo.png',
                srcDark: 'img/logo-for-dark.png'
            },
            items: [
                {
                    position: 'left',
                    label: 'Documents',
                    to: '/docs/intro',
                },
                {
                    to: 'pathname:///agda_html/Peras.SmallStep.html',
                    label: 'Formal Specification',
                    position: 'left'
                },
                {
                    to: '/weekly',
                    label: 'Updates',
                    position: 'left'
                },
                {
                    to: 'https://github.com/cardano-foundation/CIPs/blob/master/CIP-0140/README.md',
                    label: 'CIP',
                    position: 'right',
                },
                {
                    to: 'pathname:///dashboard/index.html',
                    label: 'Dashboard',
                    position: 'right',
                },
                {
                    href: 'https://peras-simulation.cardano-scaling.org/',
                    label: 'Simulator',
                    position: 'right',
                },
                {
                    href: 'https://github.com/input-output-hk/peras-design',
                    label: 'GitHub',
                    position: 'right',
                },
            ],
        },
        footer: {
            links: [
                {
                    title: 'Docs',
                    items: [
                        {
                            label: 'Documents',
                            to: '/docs/intro',
                        },
                    ],
                },
                {
                    title: 'Community',
                    items: [
                        {
                            label: 'Discord',
                            href: 'https://discord.gg/9EgySPJk',
                        },
                        {
                            label: 'GitHub Discussions',
                            href: 'https://github.com/input-output-hk/peras-design/discussions',
                        },
                    ],
                },
                {
                    title: 'More',
                    items: [
                        {
                            label: 'Updates',
                            to: '/weekly',
                        },
                        {
                            label: 'GitHub',
                            href: 'https://github.com/input-output-hk/peras-design',
                        },
                    ],
                },
                {
                    title: "Legal",
                    items: [
                        {
                            label: "Terms & Conditions",
                            to: "https://static.iohk.io/terms/iohktermsandconditions.pdf",
                        },
                        {
                            label: "Privacy Policy",
                            to: "https://static.iohk.io/terms/iog-privacy-policy.pdf",
                        },
                        {
                            label: "Contributors",
                            to: "https://github.com/input-output-hk/peras-design/graphs/contributors",
                        },
                    ],
                },
            ],
            copyright: `Copyright © ${new Date().getFullYear()} <strong>Input Output Global</strong> <br/> <a href="https://static.iohk.io/terms/iog-privacy-policy.pdf" target="_blank" class="footer__link-item">Privacy Policy</a> | <a href="https://static.iohk.io/terms/iohktermsandconditions.pdf" target="_blank" class="footer__link-item">Terms & Conditions</a> <br/> <small>Built with Docusaurus</small>`,
        },
        prism: {
            theme: prismThemes.github,
            darkTheme: prismThemes.dracula,
        },
    } satisfies Preset.ThemeConfig,
};

export default config;
