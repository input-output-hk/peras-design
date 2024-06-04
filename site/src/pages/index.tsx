import clsx from 'clsx';
import Link from '@docusaurus/Link';
import useDocusaurusContext from '@docusaurus/useDocusaurusContext';
import Layout from '@theme/Layout';
import Heading from '@theme/Heading';
import { useColorMode } from '@docusaurus/theme-common';


import styles from './index.module.css';
import FeaturesList from '../components/FeaturesList';

import HeaderBorderTop from '@site/static/img/hero-border-top.svg';
import HeaderBorderBottom from '@site/static/img/hero-border-bottom.svg';

import HeaderBorderTopDark from '@site/static/img/hero-border-top-dark.svg';
import HeaderBorderBottomDark from '@site/static/img/hero-border-bottom-dark.svg';


function HomepageHeader() {
    const { siteConfig } = useDocusaurusContext();
    const { isDarkTheme } = useColorMode();  

    return (
    <>
    <div style={{width: "100%", display: "flex"}}>
        {isDarkTheme ? <HeaderBorderTopDark style={{height: "auto"}} /> : <HeaderBorderTop style={{height: "auto"}}/>}
        </div>
            <header className={clsx('hero hero--primary', styles.heroBanner)}>
                <div className="container">
                    <Heading as="h1" className="hero__title">
                        {siteConfig.title}
                    </Heading>
                    <p className={clsx(styles.heroSubtitle)}>{siteConfig.tagline}</p>
                        <Link
                            className={clsx("button button--secondary button--lg", styles.ctaButton)}
                            to="/docs/intro">
                            Peras Tutorial - 5min ⏱️
                        </Link>
                </div>
            </header>
            <div style={{width: "100%", display: "flex"}}>
         {isDarkTheme ? <HeaderBorderBottomDark style={{height: "auto"}} /> : <HeaderBorderBottom style={{height: "auto"}}/>}
        </div>
        </>
    );
}

export default function Home(){
    const { siteConfig } = useDocusaurusContext();
    return (
        <Layout
            title={`${siteConfig.title}`}
            description="Description will go into a meta tag in <head />">
            <HomepageHeader />
            <main>
                <FeaturesList/>
            </main>
        </Layout>
    );
}