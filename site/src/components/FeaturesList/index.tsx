import React from 'react';
import Feature from '../Feature'
import styles from './styles.module.css';
import Secure from '@site/static/img/security.svg';
import Lightweight from '@site/static/img/lightweight.svg';
import Fast from '@site/static/img/fast.svg';
import clsx from 'clsx';

function FeaturesList() {
  const features = [
    {
        Icon: Lightweight,
      title: 'Lightweight Design',
      description: 'Utilizes a weighted voting mechanism to minimize resource usage, making it efficient and scalable.',
    },
    {
      Icon: Fast,
      title: 'Fast Settlement',
      description: 'Reduces transaction confirmation time from hours to minutes.',
    },
    {
        Icon: Secure,
      title: 'Robust Security',
      description: 'Maintains the security guarantees of Ouroboros Praos while adapting its defenses based on network conditions and threats.',
    },
  ];

  return (
    <section className={clsx('container',styles.featuresContainer)}>
      <div className="container">
        <div className="row">
      {features.map((feature, index) => (
        <Feature key={index} {...feature} />
      ))}
        </div>
      </div>
    </section>
  );
}

export default FeaturesList;