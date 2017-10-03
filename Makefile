VOLUMES:=lf plf vfa

.PHONY: all clean html

all:
	for volume in $(VOLUMES); do cd $$volume && make && cd .. ; done

html:
	for volume in $(VOLUMES); do cd $$volume && make html && cd .. && rm -rf html/$$volume && cp -r $$volume/html html/$$volume ; done

clean:
	for volume in $(VOLUMES); do cd $$volume && make clean && cd .. ; done
	for volume in $(VOLUMES); do rm -rf html/$$volume ; done
