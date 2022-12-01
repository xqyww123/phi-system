BUILD_DIR:=/tmp/CoP
TSDIR=timestamps/$(shell git rev-parse HEAD)
TS_SERVERS=https://freetsa.org/tsr \
	http://rfc3161timestamp.globalsign.com/advanced \
	http://timestamp.sectigo.com \
	http://time.certum.pl \
	http://timestamp.digicert.com \
	http://zeitstempel.dfn.de \
	https://www.safestamper.com/tsa \
	http://timestamp.apple.com/ts01 \
	http://timestamp.entrust.net/TSS/RFC3161sha2TS

.PHONY: timestamp sup_mat CoP all sup_mat_local

all:
	rsync . $(BUILD_DIR) --exclude=.git -r -L
	(cd $(BUILD_DIR) && make CoP)

sup_mat:
	rsync . $(BUILD_DIR) --exclude=.git -r -L
	(cd $(BUILD_DIR) && make sup_mat_local)

CoP:
	xelatex -shell-escape CoP 
	#makeindex CoP.idx
	bibtex CoP
	#xelatex -shell-escape CoP
	#xelatex -shell-escape CoP

sup_mat_local:
	xelatex -shell-escape sup_mat
	#makeindex CoP.idx

clean:
	(cd $(BUILD_DIR) && make clean-here)

clean-here:
	rm -f *.aux *.bbl *.blg *.idx *.ilg *.ind *.lof *.log *.lot *.out *.toc

timestamp:
	mkdir -p $(TSDIR)
	cp $(BUILD_DIR)/CoP.pdf $(TSDIR)/paper.pdf
	openssl ts -query -data $(TSDIR)/paper.pdf -sha512 -out $(TSDIR)/paper.tsq
	openssl ts -query -digest $(shell cat $$(git ls-files -z | tr '\000' '\n') | sha512sum | cut -d " " -f1) -no_nonce -sha512 -out $(TSDIR)/commit.tsq
	for url in $(TS_SERVERS) ; do \
		curl -H "Content-Type: application/timestamp-query" --data-binary '@$(TSDIR)/commit.tsq' $$url > $(TSDIR)/commit.$$(echo $$url | cut -d'/' -f3).tsr ; \
		curl -H "Content-Type: application/timestamp-query" --data-binary '@$(TSDIR)/paper.tsq' $$url > $(TSDIR)/paper.$$(echo $$url | cut -d'/' -f3).tsr ; \
	done
