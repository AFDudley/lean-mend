/*
  The commit-boundary gate image for lean-mend, built with Nix via
  nix2container (docs/plans/nix-images.md T3.lean; D1-D11). Layout
  mirrors armada-lean's own nix/gate.nix and exophial's own nix/gate.nix:
  explicit layers, each keyed on its own inputs, plus one per-commit
  layer carrying the judged tree.

    toolsLayer    system tools, the elan-less Lean v4.29.0/v4.33.1/
                  v4.35.0 dispatch (nix/lean.nix -- lean-mend's own
                  tests/probe-matrix.sh runs all three), jq (the probe
                  matrix checks), pre-commit-hooks 4.6.0 (D6's 7 local
                  "Base hooks"), and the exophial flake input's own
                  `exophial` package (its 5 local-hook console scripts)
    per commit    the judged tree at /gate, verbatim

  Nothing downloads at container run time (D11): lean-mend's own
  `lake-manifest.json` carries no dependency (packages: []), so its
  `lake build`/`lake test` never fetches anything, and no toolchain
  download replaces elan -- the three Lean releases are already image
  content. `scripts/gate.sh` itself never runs `pre-commit`; the 7 Base
  hooks and the 5 exophial-owned hooks are image content only so a
  future `gate.command` that adds `pre-commit run --all-files` needs no
  further image change (the same rationale armada-lean's own nix/gate.nix
  comment states for its own pre-commit tools).
*/
{
  pkgs,
  lib,
  n2c,
  pins,
  gateSrc,
  leanToolchains,
  exophialPkg,
}:
let
  toolPaths = [
    (pkgs.dockerTools.fakeNss.override { extraGroupLines = [ "nogroup:x:65534:" ]; })
    pkgs.bashInteractive
    pkgs.coreutils
    pkgs.gnugrep
    pkgs.gnused
    pkgs.gawk
    pkgs.findutils
    pkgs.gnutar
    pkgs.gzip
    pkgs.which
    pkgs.gitMinimal
    pkgs.jq
    pkgs.zstd
    pkgs.binutils
    pins.preCommitHooks
    leanToolchains.leanDispatch
    exophialPkg
  ];

  toolsEnv = pkgs.buildEnv {
    name = "lean-mend-gate-tools";
    paths = toolPaths;
    ignoreCollisions = true;
  };

  # The CA bundle: a safety net for any TLS client in the exophial
  # package's own dependency closure, never load-bearing for the gate's
  # own run (D11: no network at container run time).
  fhsRoot = pkgs.runCommand "lean-mend-gate-fhs-root" { } ''
    mkdir -p $out/etc/ssl/certs $out/usr/bin $out/tmp $out/lib64
    chmod 1777 $out/tmp
    ln -s ${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt $out/etc/ssl/certs/ca-certificates.crt
    # `scripts/gate.sh`'s own `#!/usr/bin/env bash` shebang (gate.command
    # execs it directly, with no shell): without this, `podman run` fails
    # with "exec scripts/gate.sh: no such file or directory" (measured
    # 2026-11-22) -- the real error is env missing, not the script.
    ln -s ${pkgs.coreutils}/bin/env $out/usr/bin/env
    # `scripts/gate.sh` compiles `lean-mend` and `tests` fresh every run
    # (lean-mend's own `lake-manifest.json` carries no dependency, so
    # unlike armada-lean nothing here restores a Nix-built artifact
    # cache). Lean's own bundled clang (the default `leanc` compiler,
    # left UNCHANGED here -- overriding it to nixpkgs' gcc hits a second
    # problem: Lean's `libleanrt.a`/`libleancpp.a` are themselves
    # compiled against a libc++ build with an internal ABI tag
    # (`[abi:nqe230100]`) that nixpkgs' own separately-built libc++ does
    # not share, so linking against a DIFFERENT libc++ fails with
    # "undefined reference" even once every `-l` name resolves. Keeping
    # the bundled clang avoids that: it already carries the matching
    # libc++ under its own `lib/clang/19/` tree. clang's produced ELF
    # still asks for the FHS dynamic linker, `/lib64/ld-linux-x86-64.so.2`
    # (measured 2026-11-22: "could not execute external process
    # '/gate/.lake/build/bin/tests'" after a clean `lake test` compile,
    # the same symptom armada-lean's own `nix/lean-deps.nix` comment
    # describes for `leanc`). This symlink is the targeted fix: it does
    # not change which compiler or which libc++ runs, only makes the
    # FHS path the produced binary's own ELF header names resolve.
    ln -s ${pkgs.glibc}/lib/ld-linux-x86-64.so.2 $out/lib64/ld-linux-x86-64.so.2
  '';

  # The judged tree, placed AT /gate: `copyToRoot` merges a listed
  # path's own CONTENTS at the image root, so `gateSrc` itself (a plain
  # checkout directory) would land its files at `/`, not `/gate` -- this
  # wrapper is what actually puts them at `/gate`.
  gateTree = pkgs.runCommand "lean-mend-gate-tree" { } ''
    mkdir -p $out/gate
    cp -r ${gateSrc}/. $out/gate/
  '';

  toolsLayer = n2c.buildLayer { copyToRoot = [ toolsEnv ]; };
  fhsLayer = n2c.buildLayer {
    copyToRoot = [ fhsRoot ];
    layers = [ toolsLayer ];
  };
in
n2c.buildImage {
  name = "localhost/lean-mend-gate";
  layers = [
    toolsLayer
    fhsLayer
  ];
  copyToRoot = [ gateTree ];
  config = {
    WorkingDir = "/gate";
    Env = [
      "PATH=/bin"
      "HOME=/root"
      "SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
    ];
  };
}
