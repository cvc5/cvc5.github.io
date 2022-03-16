---
layout: default
---

# Awards

## Competitions

{% for competition in site.data.awards.competitions %}

### {{ competition.name }}

{% assign years = competition.events | map: "year" | uniq | sort | reverse %}
{% for year in years %}
{% assign yearStr = year | append: "" %}
{% assign yearInt = year | plus: 0 %}
{% assign entries = competition.events | where_exp: "e","e.year == year" %}
{% for item in entries %}
- [{{ item.event }}]({{ item.event_url }})
  ([details]({{ item.details | relative_url }}))
  - <b>entered:</b> {{ item.entered.divisions }} divisions
  - <b>overall:</b> {{ item.gold.divisions | plus: item.gold.competition-wide }} gold medals
  - <b>division awards:</b> {{ item.gold.divisions }} gold medals (out of {{ item.entered.awards }})
  - <b>competition-wide awards:</b> {{ item.gold.competition-wide }} gold medals
{% endfor %}
{% endfor %}

{% endfor %}



