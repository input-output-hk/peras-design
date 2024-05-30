import clsx from 'clsx';
import Heading from '@theme/Heading';
import styles from './styles.module.css';

type FeatureItem = {
    title: string;
    Svg: React.ComponentType<React.ComponentProps<'svg'>>;
    description: JSX.Element;
};

const FeatureList: FeatureItem[] = [
    {
        title: 'Easy to Use',
        Svg: require('@site/static/img/undraw_docusaurus_mountain.svg').default,
        description: (
            <>
                Docusaurus was designed from the ground up to be easily installed and
                used to get your website up and running quickly.
            </>
        ),
    },
    {
        title: 'Focus on What Matters',
        Svg: require('@site/static/img/undraw_docusaurus_tree.svg').default,
        description: (
            <>
                Docusaurus lets you focus on your docs, and we&apos;ll do the chores. Go
                ahead and move your docs into the <code>docs</code> directory.
            </>
        ),
    },
    {
        title: 'Powered by React',
        Svg: require('@site/static/img/undraw_docusaurus_react.svg').default,
        description: (
            <>
                Extend or customize your website layout by reusing React. Docusaurus can
                be extended while reusing the same header and footer.
            </>
        ),
    },
];

function Feature({ title, Svg, description }: FeatureItem) {
    return (
        <div className={clsx('col col--4')}>
            <div className="text--center">
                <Svg className={styles.featureSvg} role="img" />
            </div>
            <div className="text--center padding-horiz--md">
                <Heading as="h3">{title}</Heading>
                <p>{description}</p>
            </div>
        </div>
    );
}

export default function HomepageFeatures(): JSX.Element {
    return (
        <section className={styles.features}>
            <div className="container">
                <div className="row">
                    <div className={clsx('col col--4 text--center')}>
                        <img className={styles.featureSvg} src={ouroboros} />
                    </div>
                    <div className={clsx('col col--8 text--center')}>
                        <h3>Faster Settlement for Ouroboros</h3>
                        <p>Ouroboros Peras is adaptively secure and provides fast settlement for Ouroboros, overcoming a well known issue with Nakamoto-style consensus. At its core it is based on <em>weights</em>,  calling for participants to repeatedly vote on a recent but not too recent block on their chain. While each block has unit base weight, any block with a sufficient number of votes receives a significant weight boost. The new protocol achieves fast settlement when the adversary controls less than 1/4 of the stake, and maintains safety against an adversary controlling up to 1/2 of the stake.</p>
                    </div>
                </div>
            </div>
        </section>
    );
}
