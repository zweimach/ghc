TOP=../..
include $(TOP)/mk/boilerplate.mk
include $(TOP)/mk/test.mk

# Each of the tests also exercise the various ways to bring plugins into scope

# -hide-all-plugin-packages + -plugin-package
.PHONY: plugins01
plugins01:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins01.hs -package-db simple-plugin/pkg.plugins01/local.package.conf -fplugin Simple.Plugin -fplugin-opt Simple.Plugin:Irrelevant_Option -hide-all-plugin-packages -plugin-package simple-plugin
	./plugins01

# -hide-all-packages + -plugin-package
.PHONY: plugins07
plugins07:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 -O plugins07.hs -package-db rule-defining-plugin/pkg.plugins07/local.package.conf -hide-all-packages -package base -plugin-package rule-defining-plugin -fplugin=RuleDefiningPlugin
	./plugins07

.PHONY: plugins08
plugins08:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins08.hs -package-db simple-plugin/pkg.plugins08/local.package.conf
	./plugins08

.PHONY: plugins09
plugins09:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins09.hs -package-db simple-plugin/pkg.plugins09/local.package.conf -fplugin Simple.SourcePlugin -fplugin-opt Simple.SourcePlugin:a -fplugin-opt Simple.SourcePlugin:b -plugin-package simple-plugin

.PHONY: plugins10
plugins10:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins10.hs QuasiQuotation.hs -package-db simple-plugin/pkg.plugins10/local.package.conf -fplugin Simple.SourcePlugin -plugin-package simple-plugin

.PHONY: plugins11
plugins11:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins11.hs -package-db simple-plugin/pkg.plugins11/local.package.conf -plugin-package simple-plugin

.PHONY: plugins12
plugins12:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins12.hs -package-db simple-plugin/pkg.plugins12/local.package.conf -plugin-package simple-plugin

.PHONY: plugins13
plugins13:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins13.hs PluginFilteredExport.hs -package-db simple-plugin/pkg.plugins13/local.package.conf -plugin-package simple-plugin

.PHONY: plugins14
plugins14:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins14.hs -package-db simple-plugin/pkg.plugins14/local.package.conf -plugin-package simple-plugin

.PHONY: plugins15
plugins15:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 plugins15.hs MetaRemoveHelper.hs -package-db simple-plugin/pkg.plugins15/local.package.conf -plugin-package simple-plugin

# -package (should work for backwards compatibility)
.PHONY: T10420
T10420:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 -O T10420.hs -package-db rule-defining-plugin/pkg.T10420/local.package.conf -hide-all-packages -package base -package rule-defining-plugin
	./T10420

.PHONY: T10294
T10294:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) -c -v0 T10294.hs -package-db annotation-plugin/pkg.T10294/local.package.conf -package annotation-plugin -fplugin=SayAnnNames

.PHONY: T10294a
T10294a:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) -c -v0 T10294a.hs -package-db annotation-plugin/pkg.T10294a/local.package.conf -package annotation-plugin -fplugin=SayAnnNames

.PHONY: frontend01
frontend01:
	$(RM) FrontendPlugin.hi FrontendPlugin.o frontend01 frontend01.hi frontend.o
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) -Wall -package ghc -c FrontendPlugin.hs
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --frontend FrontendPlugin -ffrontend-opt foo -ffrontend-opt bar frontend01
	./frontend01

# -hide-all-plugin-packages + -package (this should not work!)
.PHONY: T11244
T11244:
	! "$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 -O T11244.hs -package-db rule-defining-plugin/pkg.T11244/local.package.conf -hide-all-plugin-packages -package rule-defining-plugin -fplugin=RuleDefiningPlugin

.PHONY: T12567a
T12567a:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make T12567a.hs -package-db simple-plugin/pkg.T12567a/local.package.conf -hide-all-plugin-packages -plugin-package simple-plugin 1>&2
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make T12567a.hs -package-db simple-plugin/pkg.T12567a/local.package.conf -hide-all-plugin-packages -plugin-package simple-plugin 1>&2
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make T12567b.hs -package-db simple-plugin/pkg.T12567a/local.package.conf -hide-all-plugin-packages -plugin-package simple-plugin 1>&2

.PHONY: T14335
T14335:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) -fexternal-interpreter --make -v0 plugins01.hs -package-db simple-plugin/pkg.plugins01/local.package.conf -fplugin Simple.Plugin -fplugin-opt Simple.Plugin:Irrelevant_Option -hide-all-plugin-packages -plugin-package simple-plugin
	./plugins01

# Shouldn't recompile the module
.PHONY: plugin-recomp-pure
plugin-recomp-pure:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin PurePlugin
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin PurePlugin

# Should recompile the module
.PHONY: plugin-recomp-impure
plugin-recomp-impure:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin ImpurePlugin
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin ImpurePlugin

# Should not recompile the module the first time but should the second time
.PHONY: plugin-recomp-flags
plugin-recomp-flags:
	"$(TEST_HC)" $(TEST_HC_OPTS)  $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin FingerprintPlugin -fplugin-opt FingerprintPlugin:0
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin FingerprintPlugin -fplugin-opt FingerprintPlugin:0
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin FingerprintPlugin -fplugin-opt FingerprintPlugin:1
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) plugin-recomp-test.hs -package-db plugin-recomp/pkg.plugins01/local.package.conf -fplugin FingerprintPlugin -fplugin-opt FingerprintPlugin:1

.PHONY: exprtype01
exprtype01:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:10:9-10:36 -package-db simple-plugin/pkg.exprtype01/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype02
exprtype02:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:12:9-12:36 -package-db simple-plugin/pkg.exprtype02/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype03
exprtype03:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:14:9-14:44 -package-db simple-plugin/pkg.exprtype03/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype04
exprtype04:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:16:11-17:35 -package-db simple-plugin/pkg.exprtype04/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype05
exprtype05:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:19:9-19:27 -package-db simple-plugin/pkg.exprtype05/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype06
exprtype06:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:21:9-21:18 -package-db simple-plugin/pkg.exprtype06/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype07
exprtype07:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:23:9-24:23 -package-db simple-plugin/pkg.exprtype07/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype08
exprtype08:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:26:11-27:50 -package-db simple-plugin/pkg.exprtype08/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype09
exprtype09:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:29:9-29:25 -package-db simple-plugin/pkg.exprtype09/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype10
exprtype10:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:31:10-31:11 -package-db simple-plugin/pkg.exprtype10/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype11
exprtype11:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:33:10-33:13 -package-db simple-plugin/pkg.exprtype11/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype12
exprtype12:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:35:10-35:17 -package-db simple-plugin/pkg.exprtype12/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype13
exprtype13:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:38:10-38:36 -package-db simple-plugin/pkg.exprtype13/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype14
exprtype14:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:40:10-40:37 -package-db simple-plugin/pkg.exprtype14/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype15
exprtype15:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:42:10-42:15 -package-db simple-plugin/pkg.exprtype15/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype16
exprtype16:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:44:10-44:15 -package-db simple-plugin/pkg.exprtype16/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype17
exprtype17:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:46:10-46:27 -package-db simple-plugin/pkg.exprtype17/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype18
exprtype18:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:48:10-48:15 -package-db simple-plugin/pkg.exprtype18/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype19
exprtype19:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:50:10-50:18 -package-db simple-plugin/pkg.exprtype19/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype20
exprtype20:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:52:10-52:17 -package-db simple-plugin/pkg.exprtype20/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype21
exprtype21:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:54:10-54:18 -package-db simple-plugin/pkg.exprtype21/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype22
exprtype22:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:56:10-56:15 -package-db simple-plugin/pkg.exprtype22/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype23
exprtype23:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:58:10-58:18 -package-db simple-plugin/pkg.exprtype23/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype24
exprtype24:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:60:10-60:12 -package-db simple-plugin/pkg.exprtype24/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype25
exprtype25:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:62:10-63:24 -package-db simple-plugin/pkg.exprtype25/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype26
exprtype26:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:65:10-66:25 -package-db simple-plugin/pkg.exprtype26/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype27
exprtype27:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:68:10-68:21 -package-db simple-plugin/pkg.exprtype27/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype28
exprtype28:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:71:10-71:16 -package-db simple-plugin/pkg.exprtype28/local.package.conf -plugin-package simple-plugin

.PHONY: exprtype29
exprtype29:
	"$(TEST_HC)" $(TEST_HC_OPTS) $(ghcPluginWayFlags) --make -v0 exprtype.hs -fplugin-opt Simple.ExprTypePlugin:74:10-74:11 -package-db simple-plugin/pkg.exprtype29/local.package.conf -plugin-package simple-plugin
