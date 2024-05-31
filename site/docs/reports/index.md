---
sidebar_label: 'Reports'
sidebar_position: 1
---

# Reports

This page groups "reports" on the project's results.

```mdx-code-block
import DocCardList from '@theme/DocCardList';
import {useDocsSidebar} from '@docusaurus/theme-common/internal';

<DocCardList items={useDocsSidebar().items.filter(({ docId }) => docId != "index")}/>
```
