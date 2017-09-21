
VOLUMES:=lf plf vfa

.PHONY: all clean html

all:
	for volume in $(VOLUMES); do cd $$volume && make && cd .. ; done

html:
	for volume in $(VOLUMES); do cd $$volume && make html && cd .. ; done

clean:
	for volume in $(VOLUMES); do cd $$volume && make clean && cd .. ; done
