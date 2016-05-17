TOP=../../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

T8308:
	@'$(TEST_HC)' $(TEST_HC_OPTS) -rtsopts -ticky -O0 T8308.hs &>/dev/null
	@./T8308 +RTS -rT8308.ticky &>/dev/null
	@grep RET_NEW_hst_1 T8308.ticky | awk '{ print $$1 }'

.PHONY: T8308
