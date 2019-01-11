######################################################
ORG=ucsd-cse230-wi19
ASGN=hw1
######################################################

check: src/Hw1.hs
	stack exec -- liquid src/Hw1.hs 

tags:
	hasktags -x -c lib/

turnin: 
	git commit -a -m "turnin"
	git push origin master

upstream:
	git remote add upstream git@github.com:$(ORG)/$(ASGN).git

update:
	git pull upstream master
