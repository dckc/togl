
docs/picalc2.html: picalc2.lidr
	pandoc  --from markdown+lhs --to html --katex --standalone -o $@ $<
