# Package

version       = "0.2.13"
author        = "haxscramper"
description   = "Nim term rewriting system"
license       = "Apache-2.0"
srcDir        = "src"



# Dependencies

requires "nim >= 1.2.4"
requires "hmisc", "hdrawing", "hpprint", "hnimast"

let
  testDir = "/tmp/docker-hpprint"
  localDevel = @["hmisc", "hpprint", "hnimast", "hmisc"]

template canImport(x: untyped): untyped =
  compiles:
    import x


when canImport(hmisc/other/nimbleutils):
  import hmisc/other/nimbleutils

  task dockertestDevel, "Test in docker container with local packages":
    runDockerTestDevel(
      thisDir(), testDir, localDevel, "nimble test") do:
        writeTestConfig("""
          --verbosity:0
          --hints:off
          --warnings:off
        """)

    rmDir testDir


  task dockertestAllDevel, "Test in docker container with local packages":
    runDockerTestDevel(
      thisDir(), testDir, localDevel, "nimble testallTask") do:
        writeTestConfig("""
          --verbosity:0
          --hints:off
          --warnings:off
        """)

  task dockertest, "Test in new docker container":
    ## Run unit tests in new docker conatiner; download all
    ## dependencies using nimble.
    runDockerTest(thisDir(), testDir, "nimble test") do:
      notice "Running test in docker container"

  task installtest, "Test installation from cloned repo":
    runDockerTest(thisDir(), testDir, "nimble install")

  task testall, "Run full test suite in all variations":
    runDockerTest(
      thisDir(), testDir,
      "nimble install -n hmisc@#head && nimble testallTask")

  task testallTask, "~~~ testall implementation ~~~":
    testAllImpl()
