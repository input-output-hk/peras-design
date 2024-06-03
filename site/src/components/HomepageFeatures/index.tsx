import clsx from 'clsx';
import Heading from '@theme/Heading';
import styles from './styles.module.css';
import fast_slow from '/static/img/fast-slow.jpeg';

export default function HomepageFeatures(): JSX.Element {
    return (
        <section className={styles.features}>
            <div className="container">
                <div className="row">
                    <div className={clsx('col col--4 text--center')}>
                        <img className={styles.featureSvg} src={fast_slow} />
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
