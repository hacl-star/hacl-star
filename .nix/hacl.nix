{
  bash,
  dotnet-runtime,
  fetchFromGitHub,
  fstar,
  fstar-scripts,
  git,
  karamel,
  lib,
  ocamlPackages,
  openssl,
  python3,
  rustc,
  sd,
  stdenv,
  time,
  vale,
  which,
  writeTextFile,
  z3,
}: let
  runlim = stdenv.mkDerivation rec {
    name = "runlim";
    src = fetchFromGitHub {
      owner = "arminbiere";
      repo = "runlim";
      rev = "3821e7a1d1ada328cda7a9cff33ea13228d8013a";
      sha256 = "sha256-f1jp83GDrRjqEqXEDW2eD6IJzI53pBFkp+qOdpOR6sc=";
    };
    configurePhase = ''
      CC="" ./configure.sh
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp ./runlim ./runlim-remount-proc $out/bin
    '';
  };

  hacl = stdenv.mkDerivation {
    name = "hacl-star";

    src = lib.cleanSourceWith {
      src = ./..;
      filter = path: type: let
        relPath = lib.removePrefix (toString ./.. + "/") (toString path);
      in
        type
        == "directory"
        || lib.elem relPath [
          ".gitignore"
          "Makefile"
          "Makefile.common"
          "Makefile.include"
          "Makefile.openssl"
          "dist/LICENSE.txt"
          "dist/META"
          "dist/Makefile.test"
          "dist/Makefile.tmpl"
          "dist/configure"
          "dist/package-mozilla.sh"
        ]
        || lib.any (lib.flip lib.hasPrefix relPath) [
          "code"
          "hints"
          "lib"
          "providers"
          "secure_api"
          "specs"
          "tests"
          "tools"
          "vale"
        ];
    };

    postPatch = ''
      patchShebangs tools
      patchShebangs dist/configure
      patchShebangs dist/package-mozilla.sh
      substituteInPlace Makefile --replace "NOSHORTLOG=1" ""
      echo "0.3.19" > vale/.vale_version
    '';

    nativeBuildInputs =
      [
        z3
        fstar
        python3
        which
        dotnet-runtime
        time
        runlim
        rustc
      ]
      ++ (with ocamlPackages; [
        ocaml
        findlib
        batteries
        pprint
        stdint
        yojson
        zarith
        ppxlib
        ppx_deriving
        ppx_deriving_yojson
        ctypes
        cppo
        alcotest
        qcheck-core
        secp256k1-internal
        menhirLib
        process
        sedlex
      ]);

    buildInputs = [openssl.dev];

    VALE_HOME = vale;
    FSTAR_HOME = fstar;
    KRML_HOME = karamel;

    configurePhase = "export HACL_HOME=$(pwd)";

    enableParallelBuilding = true;

    buildPhase = ''
      RESOURCEMONITOR=1 make -j$NIX_BUILD_CORES ci 2>&1 | tee log.txt
      bash ${fstar-scripts}/remove_stale_hints.sh
    '';

    installPhase = ''
      cp -r ./. $out
    '';

    dontFixup = true;

    passthru = rec {
      info = writeTextFile {
        name = "INFO.txt";
        text = ''
          This code was generated with the following toolchain.
          F* version: ${fstar.version}
          Karamel version: ${karamel.version}
          Vale version: ${vale.version}
        '';
      };
      dist-compare = stdenv.mkDerivation {
        name = "hacl-diff-compare";
        src = "${hacl.build-products}/dist.tar.gz";
        phases = ["unpackPhase" "buildPhase" "installPhase"];
        buildPhase = ''
          for file in ./*/*.c ./*/*.h
          do
            if ! diff $file ${../dist}/$file 2>&1 > /dev/null
            then
              echo "*** $file"
              diff -y --suppress-common-lines $file ${../dist}/$file || true
            fi
          done
        '';
        installPhase = ''
          touch $out
        '';
      };
      dist-list = stdenv.mkDerivation {
        name = "hacl-diff-list";
        src = "${hacl.build-products}/dist.tar.gz";
        phases = ["unpackPhase" "buildPhase" "installPhase"];
        buildPhase = ''
          diff -rq . ${../dist} 2>&1 \
            | sed 's/\/nix\/store\/[a-z0-9]\{32\}-//g' \
            | sed 's/^Files \([^ ]*\).*/\1/' \
            | sed 's/^Only in source\/dist\([^\:]*\)\: \(.*\)/\.\1\/\2/' \
            | sed 's/^Only in \.\([^\:]*\)\: \(.*\)/\.\1\/\2/' \
            | { grep '\.\/[^\/]*\/' || true; } \
            | { grep -v INFO.txt || true; }
        '';
        installPhase = ''
          touch $out
        '';
      };
      build-products = stdenv.mkDerivation {
        name = "hacl-build-products";
        src = hacl;
        buildInputs = [git sd];
        buildPhase = ''
          sd '${bash}/bin/bash' '/usr/bin/env bash' dist/configure
          sd '${bash}/bin/bash' '/usr/bin/env bash' dist/package-mozilla.sh
          for target in gcc-compatible msvc-compatible portable-gcc-compatible mozilla
          do
            sd '${bash}/bin/bash' '/usr/bin/env bash' dist/$target/configure
          done

          for target in gcc-compatible mozilla msvc-compatible portable-gcc-compatible wasm
          do
            cp ${info} dist/$target/INFO.txt
          done

          git init
          git config --local user.name "John Doe"
          git config --local user.email johndoe@example.com
          git add *
          git commit -m "initial commit"

          git archive HEAD hints -o hints.tar.gz
          git archive HEAD dist/* -o dist.tar.gz
        '';
        installPhase = ''
          mkdir -p $out
          cp hints.tar.gz dist.tar.gz $out
        '';
      };
      stats = stdenv.mkDerivation {
        name = "hacl-stats";
        phases = ["installPhase"];
        installPhase = ''
          mkdir -p $out
          cat ${hacl}/log.txt \
              | grep "^\[VERIFY\]" \
              | sed 's/\[VERIFY\] \(.*\), \(.*\)/\2 \1/' \
              | sort -rg - > $out/stats.txt
        '';
      };
      resource-monitor = stdenv.mkDerivation {
        name = "hacl-resource-monitor";
        src = hacl;
        dontBuild = true;
        installPhase = ''
          mkdir -p $out
          bash ${fstar-scripts}/res_summary.sh > $out/resources.txt
        '';
      };
    };
  };
in
  hacl
