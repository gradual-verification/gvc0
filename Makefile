clean:
	@rm -f executionTreeData.js
	@rm -f executionTreeData.txt
	@rm -rf ./tmp
	@rm -rf ./*.dSYM
	@rm -rf ./*.dot
	@rm -rf ./*.c0.c
	@rm -rf ./*.c0.h
	@rm -rf ./*.vpr
	@rm -rf ./*.ir.c0
	@rm -rf ./*.verified.c0
clean-data:
	@rm -rf ./data/compiled/
data: clean-data
	@mkdir ./data/compiled
	@Rscript ./data/compile.r ./data/results/ ./data/compiled