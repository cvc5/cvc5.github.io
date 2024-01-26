---
layout: default
title: Blog
---

# Blog

Updates are posted every other month, sometimes more frequently. 


{% for post in site.posts %}
  <h2><a href="{{ post.url }}">{{ post.title }}</a></h2>
  <p>by {{ post.author }}, {{ post.date | date_to_string }} <p> </p> {{ post.excerpt | strip_html }}
    <a href="{{ post.url }}" class="read-more">Read More</a> </p>
{% endfor %}
