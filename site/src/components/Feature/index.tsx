import React from 'react';
import styles from './styles.module.css';
import clsx from 'clsx';

function Feature({ Icon, title, description }) {
    return (
      <div className={clsx('col col--4 text--center',styles.featureItem)}>
        <Icon style={{height: "125px"}} className={styles.featureIcon} /> 
        <h3 className={styles.featureTitle}>{title}</h3>
        <p className={styles.featureDescription}>{description}</p>
      </div>
    );
  }
  
  export default Feature;