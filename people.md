---
layout: default
---

# People

## Project Leaders

{% assign sorted = site.data.people.project | sort: 'lname' %}
{% for person in sorted %}{% if person.website %}[{{ person.fname }} {{ person.lname }}]({{ person.website }}) ({{ person.affiliation }}){% else %}{{ person.fname }} {{ person.lname }} ({{ person.affiliation }}){% endif %}{% if person.bio %}{{ person.bio }}{% endif %}<br/>{% endfor %}

## Senior Technical Leads

{% assign sorted = site.data.people.technical | sort: 'lname' %}
{% for person in sorted %}{% if person.website %}[{{ person.fname }} {{ person.lname }}]({{ person.website }}) ({{ person.affiliation }}){% else %}{{ person.fname }} {{ person.lname }} ({{ person.affiliation }}){% endif %}{% if person.bio %}{{ person.bio }}{% endif %}<br/>{% endfor %}

## Current Developers

{% assign sorted = site.data.people.devs | sort: 'lname' %}
{% for person in sorted %}{% if person.website %}[{{ person.fname }} {{ person.lname }}]({{ person.website }}) ({{ person.affiliation }}){% else %}{{ person.fname }} {{ person.lname }} ({{ person.affiliation }}){% endif %}<br/>{% endfor %}
