---
layout: default
title: publications
---

# Publications


If you are citing cvc5, please use
<a href="https://dblp.org/rec/conf/tacas/BarbosaBBKLMMMN22.html?view=bibtex">
the following BibTex entry
</a>:
<pre>
@inproceedings{DBLP:conf/tacas/BarbosaBBKLMMMN22,
  author    = {Haniel Barbosa and
               Clark W. Barrett and
               Martin Brain and
               Gereon Kremer and
               Hanna Lachnitt and
               Makai Mann and
               Abdalrhman Mohamed and
               Mudathir Mohamed and
               Aina Niemetz and
               Andres N{\"{o}}tzli and
               Alex Ozdemir and
               Mathias Preiner and
               Andrew Reynolds and
               Ying Sheng and
               Cesare Tinelli and
               Yoni Zohar},
  editor    = {Dana Fisman and
               Grigore Rosu},
  title     = {cvc5: {A} Versatile and Industrial-Strength {SMT} Solver},
  booktitle = {Tools and Algorithms for the Construction and Analysis of Systems
               - 28th International Conference, {TACAS} 2022, Held as Part of the
               European Joint Conferences on Theory and Practice of Software, {ETAPS}
               2022, Munich, Germany, April 2-7, 2022, Proceedings, Part {I}},
  series    = {Lecture Notes in Computer Science},
  volume    = {13243},
  pages     = {415--442},
  publisher = {Springer},
  year      = {2022},
  url       = {https://doi.org/10.1007/978-3-030-99524-9\_24},
  doi       = {10.1007/978-3-030-99524-9\_24},
  timestamp = {Fri, 01 Apr 2022 15:49:27 +0200},
  biburl    = {https://dblp.org/rec/conf/tacas/BarbosaBBKLMMMN22.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org},
}
</pre>

{% assign years = site.data.publications.references
  | map: "issued"
  | map: "year"
  | where_exp: 'y', 'y > 2015'
  | uniq | sort | reverse %}

{% assign books = site.data.publications.references
  | where_exp: 'r', "r.type == 'book'" %}
{% assign book_chapters = site.data.publications.references
  | where_exp: 'r', "r.type == 'chapter'" %}
{% assign articles = site.data.publications.references
  | where_exp: 'r', "r.type == 'article-journal'" %}
{% assign papers = site.data.publications.references
  | where_exp: 'r', "r.type == 'paper-conference'" %}
{% assign reports = site.data.publications.references
  | where_exp: 'r', "r.type == 'report'" %}
{% assign theses = site.data.publications.references
  | where_exp: 'r', "r.type == 'thesis'" %}

{% for year in years %}

## {{ year }}

{% assign ybooks = books
  | where_exp: 'r', 'r.issued[0].year == year' %}
{% assign ychapters = book_chapters
  | where_exp: 'r', 'r.issued[0].year == year' %}
{% if ybooks.size > 0 or ychapters.size > 0 %}
### Books and Book Chapters
{% assign months = ybooks
  | map: "issued"
  | map: "month"
  | uniq | sort | reverse %}
{% for month in months %}
{% assign mbooks = ybooks
  | where_exp: 'r', 'r.issued[0].month == month' %}
{% for item in mbooks %}
{% capture title %}{% assign t = item.title | split: ' ' %}{% for word in t %}{{ word | capitalize }} {% endfor %}{% endcapture %}
{% if item.url %}[{{ title }}]({{ item.url }}){% else %}{{ title }} {% endif %}. Edited by {% for editor in item.editor %}{% if item.editor.size > 1 %}{% if forloop.last == true %} and {% elsif forloop.first == false %}, {% endif %}{% endif %}{{ editor.given }} {{ editor.family }}{% endfor %}. {% if item.collection-title %}{{ item.collection-title }},{% endif %}{% if item.volume %} vol. {{ item.volume }},{% endif %} {{ item.publisher }}. ({{ item.issued[0].year}})
{% endfor %}
{% endfor %}
{% assign months = ychapters
  | map: "issued"
  | map: "month"
  | uniq | sort | reverse %}
{% for month in months %}
{% assign mbooks = ychapters
  | where_exp: 'r', 'r.issued[0].month == month' %}
{% for item in mbooks %}
{% capture title %}{% assign t = item.title | split: ' ' %}{% for word in t %}{{ word | capitalize }} {% endfor %}{% endcapture %}
{% for author in item.author %}{% if item.author.size > 1 %}{% if forloop.last == true %} and {% elsif forloop.first == false %}, {% endif %}{% endif %}{{ author.given }} {{ author.family }}{% endfor %}. {% if item.url %}[{{ title }}]({{ item.url }}){% else %}{{ title }} {% endif %}. {% if item.container-title %} In {{ item.container-title }},{% endif %}{% if item.volume %} vol. {{ item.volume }},{% endif %} {% if item.collection-title %}{{ item.collection-title }},{% endif %} {% if item.editor %}({% for editor in item.editor %}{% if item.editor.size > 1 %}{% if forloop.last == true %} and {% elsif forloop.first == false %}, {% endif %}{% endif %}{{ editor.given }} {{ editor.family }}{% endfor %}, eds.),{% endif %}{% if item.page %} pp. {{ item.page }},{% endif %} {{ item.publisher }}. ({{ item.issued[0].year}})
<br />
{% if item.pdf %}<a class="btn" href="{{ item.pdf | relative_url }}">PDF</a>{% endif %} {% if item.doi %}<a class="btn" href="http://dx.doi.org/{{ item.doi }}">DOI</a>{% endif %} {% if item.preprint %}<a class="btn" href="{{ item.preprint | relative_url }}">Preprint</a>{% endif %} {% if item.extended %}<a class="btn" href="{{ item.extended | relative_url }}">Extended Version</a>{% endif %}{% if item.arxiv %}<a class="btn" href="{{ item.arxiv}}">Arxiv</a>{% endif %} {% if item.bibtex %}<a class="btn" href="{{ item.bibtex | relative_url }}">Bibtex</a>{% endif %} {% if item.artifact %}<a class="btn" href="{{ item.artifact }}">Artifact</a>{% endif %} {% if item.talk %}{% assign t = item.talk | prepend: 'talks.html#' %}<a class="btn" href="{{ t | relative_url }}">Talk</a>{% endif %} 
{% endfor %}
{% endfor %}
{% endif %}

{% assign yarticles = articles
  | where_exp: 'r', 'r.issued[0].year == year' %}
{% if yarticles.size > 0 %}
### Journal Articles
{% assign months = yarticles
  | map: "issued"
  | map: "month"
  | uniq | sort | reverse %}
{% for month in months %}
{% assign marticles = yarticles
  | where_exp: 'r', 'r.issued[0].month == month' %}
{% for item in marticles %}
{% capture title %}{% assign t = item.title | split: ' ' %}{% for word in t %}{{ word | capitalize }} {% endfor %}{% endcapture %}
{% for author in item.author %}{% if item.author.size > 1 %}{% if forloop.last == true %} and {% elsif forloop.first == false %}, {% endif %}{% endif %}{{ author.given }} {{ author.family }}{% endfor %}. {% if item.url %}[{{ title }}]({{ item.url }}){% else %}{{ title }} {% endif %}. {% if item.container-title %} In {{ item.container-title }},{% endif %}{% if item.volume %} vol. {{ item.volume }},{% endif %} {% if item.collection-title %}{{ item.collection-title }},{% endif %} {% if item.page %} pp. {{ item.page }},{% endif %} {{ item.publisher }}. ({{ item.issued[0].year}})
<br />
{% if item.pdf %}<a class="btn" href="{{ item.pdf | relative_url }}">PDF</a>{% endif %} {% if item.doi %}<a class="btn" href="http://dx.doi.org/{{ item.doi }}">DOI</a>{% endif %} {% if item.preprint %}<a class="btn" href="{{ item.preprint | relative_url }}">Preprint</a>{% endif %} {% if item.extended %}<a class="btn" href="{{ item.extended | relative_url }}">Extended Version</a>{% endif %}{% if item.arxiv %}<a class="btn" href="{{ item.arxiv}}">Arxiv</a>{% endif %} {% if item.bibtex %}<a class="btn" href="{{ item.bibtex | relative_url }}">Bibtex</a>{% endif %} {% if item.artifact %}<a class="btn" href="{{ item.artifact }}">Artifact</a>{% endif %} {% if item.talk %}{% assign t = item.talk | prepend: 'talks.html#' %}<a class="btn" href="{{ t | relative_url }}">Talk</a>{% endif %} 
{% endfor %}
{% endfor %}
{% endif %}

{% assign ypapers = papers
  | where_exp: 'r', 'r.issued[0].year == year' %}
{% if ypapers.size > 0 %}
### Conference Papers
{% assign months = ypapers
  | map: "issued"
  | map: "month"
  | uniq | sort | reverse %}
{% for month in months %}
{% assign mpapers = ypapers
  | where_exp: 'r', 'r.issued[0].month == month' %}
{% for item in mpapers %}
{% capture title %}{% assign t = item.title | split: ' ' %}{% for word in t %}{{ word | capitalize }} {% endfor %}{% endcapture %}
{% for author in item.author %}{% if item.author.size > 1 %}{% if forloop.last == true %} and {% elsif forloop.first == false %}, {% endif %}{% endif %}{{ author.given }} {{ author.family }}{% endfor %}. {% if item.url %}[{{ title }}]({{ item.url }}){% else %}{{ title }} {% endif %}. {% if item.container-title %} In {{ item.container-title }},{% endif %}{% if item.volume %} vol. {{ item.volume }},{% endif %} {% if item.collection-title %}{{ item.collection-title }},{% endif %} {% if item.page %} pp. {{ item.page }},{% endif %} {{ item.publisher }}. ({{ item.issued[0].year}}){% if item.award %}<br/><span class="awards"><strong>{{ item.award }}</strong></span>{% endif %}
<br />
{% if item.pdf %}<a class="btn" href="{{ item.pdf | relative_url }}">PDF</a>{% endif %} {% if item.doi %}<a class="btn" href="http://dx.doi.org/{{ item.doi }}">DOI</a>{% endif %} {% if item.preprint %}<a class="btn" href="{{ item.preprint | relative_url }}">Preprint</a>{% endif %} {% if item.extended %}<a class="btn" href="{{ item.extended | relative_url }}">Extended Version</a>{% endif %}{% if item.arxiv %}<a class="btn" href="{{ item.arxiv}}">Arxiv</a>{% endif %} {% if item.bibtex %}<a class="btn" href="{{ item.bibtex | relative_url }}">Bibtex</a>{% endif %} {% if item.artifact %}<a class="btn" href="{{ item.artifact }}">Artifact</a>{% endif %} {% if item.talk %}{% assign t = item.talk | prepend: 'talks.html#' %}<a class="btn" href="{{ t | relative_url }}">Talk</a>{% endif %}
{% endfor %}
{% endfor %}
{% endif %}

{% assign yreports = reports
  | where_exp: 'r', 'r.issued[0].year == year' %}
{% if yreports.size > 0 %}
### Reports
{% assign months = yreports
  | map: "issued"
  | map: "month"
  | uniq | sort | reverse %}
{% for month in months %}
{% assign mreports = yreports
  | where_exp: 'r', 'r.issued[0].month == month' %}
{% for item in mreports %}
{% capture title %}{% assign t = item.title | split: ' ' %}{% for word in t %}{{ word | capitalize }} {% endfor %}{% endcapture %}
{% for author in item.author %}{% if item.author.size > 1 %}{% if forloop.last == true %} and {% elsif forloop.first == false %}, {% endif %}{% endif %}{{ author.given }} {{ author.family }}{% endfor %}. {% if item.url %}[{{ title }}]({{ item.url }}){% else %}{{ title }} {% endif %}. ({{ item.issued[0].year}})
<br />
{% if item.pdf %}<a class="btn" href="{{ item.pdf | relative_url }}">PDF</a>{% endif %} {% if item.doi %}<a class="btn" href="http://dx.doi.org/{{ item.doi }}">DOI</a>{% endif %} {% if item.preprint %}<a class="btn" href="{{ item.preprint | relative_url }}">Preprint</a>{% endif %} {% if item.extended %}<a class="btn" href="{{ item.extended | relative_url }}">Extended Version</a>{% endif %}{% if item.arxiv %}<a class="btn" href="{{ item.arxiv}}">Arxiv</a>{% endif %} {% if item.bibtex %}<a class="btn" href="{{ item.bibtex | relative_url }}">Bibtex</a>{% endif %} {% if item.artifact %}<a class="btn" href="{{ item.artifact }}">Artifact</a>{% endif %} {% if item.talk %}{% assign t = item.talk | prepend: 'talks.html#' %}<a class="btn" href="{{ t | relative_url }}">Talk</a>{% endif %} 
{% endfor %}
{% endfor %}
{% endif %}

{% assign ytheses = theses
  | where_exp: 'r', 'r.issued[0].year == year' %}
{% if ytheses.size > 0 %}
### Theses
{% assign months = ytheses
  | map: "issued"
  | map: "month"
  | uniq | sort | reverse %}
{% for month in months %}
{% assign mtheses = ytheses
  | where_exp: 'r', 'r.issued[0].month == month' %}
{% for item in mtheses %}
{% capture title %}{% assign t = item.title | split: ' ' %}{% for word in t %}{{ word | capitalize }} {% endfor %}{% endcapture %}
{% for author in item.author %}{% if item.author.size > 1 %}{% if forloop.last == true %} and {% elsif forloop.first == false %}, {% endif %}{% endif %}{{ author.given }} {{ author.family }}{% endfor %}. {% if item.url %}[{{ title }}]({{ item.url }}){% else %}{{ title }} {% endif %}. {% if item.genre %} {{ item.genre }},{% endif %} {{ item.publisher }}. ({{ item.issued[0].year}})
<br />
{% if item.pdf %}<a class="btn" href="{{ item.pdf | relative_url }}">PDF</a>{% endif %} {% if item.doi %}<a class="btn" href="http://dx.doi.org/{{ item.doi }}">DOI</a>{% endif %} {% if item.preprint %}<a class="btn" href="{{ item.preprint | relative_url }}">Preprint</a>{% endif %} {% if item.extended %}<a class="btn" href="{{ item.extended | relative_url }}">Extended Version</a>{% endif %}{% if item.arxiv %}<a class="btn" href="{{ item.arxiv}}">Arxiv</a>{% endif %} {% if item.bibtex %}<a class="btn" href="{{ item.bibtex | relative_url }}">Bibtex</a>{% endif %} {% if item.artifact %}<a class="btn" href="{{ item.artifact }}">Artifact</a>{% endif %} {% if item.talk %}{% assign t = item.talk | prepend: 'talks.html#' %}<a class="btn" href="{{ t | relative_url }}">Talk</a>{% endif %} 
{% endfor %}
{% endfor %}
{% endif %}

{% endfor %}
