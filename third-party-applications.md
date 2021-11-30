---
layout: default
---

# Third-Party Applications

The following projects use cvc5:

{% assign sorted = site.data.third-party-applications | sort: 'name' %}
{% for project in sorted %}
- [{{ project.name }}]({{ project.url }}): {{ project.desc }}
{% endfor %}

If you use cvc5, please contact us and we'll add your application here!
