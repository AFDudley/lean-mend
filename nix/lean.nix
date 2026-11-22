/*
  The Lean toolchains this repository's gate needs, elan-less (D11):
  three pinned release tarballs, patched with autoPatchelfHook, plus a
  dispatch shim that reads a tree's own `lean-toolchain` file and execs
  the matching binary -- elan's own job, with no network and no elan.

  v4.35.0 and v4.33.1 are byte-identical construction and hashes to
  exophial's own nix/gate.nix and armada-lean's own nix/lean.nix (the
  same upstream release tarballs, so the store path is shared rather
  than rebuilt a second time). v4.29.0 is new to this migration: lean-
  mend's own `tests/probe-matrix.sh` runs the probe under all three
  versions (lean-mend/scripts/gate.sh's own comment: "elan and the
  toolchains lean-mend supports").
*/
{ pkgs, lib }:
let
  mkLean = version: hash: pkgs.stdenv.mkDerivation {
    pname = "lean4";
    inherit version;
    src = pkgs.fetchurl {
      url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-linux.tar.zst";
      inherit hash;
    };
    nativeBuildInputs = [ pkgs.autoPatchelfHook pkgs.zstd ];
    buildInputs = [ pkgs.stdenv.cc.cc.lib pkgs.gmp pkgs.libuv pkgs.zlib ];
    unpackCmd = ''
      zstd -d --stdout "$curSrc" | tar -x
    '';
    installPhase = ''
      runHook preInstall
      mkdir -p $out
      cp -r --no-preserve=ownership . $out/
      chmod -R u+w $out
      find $out/bin -maxdepth 1 -type f -exec chmod +x {} +
      runHook postInstall
    '';
  };

  lean4290 = mkLean "4.29.0" "sha256-CJ9+UT7T6UNtGR9JhjMMC1OAnIa1mX9et/JVUMN0+kg=";
  lean4331 = mkLean "4.33.1" "sha256-iQr9GFNw+FZmAluIORSrT0szkTb4yWFntpz7Yq7K8jU=";
  lean4350 = mkLean "4.35.0" "sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=";

  # toolchain name (as it appears in a `lean-toolchain` file) -> the
  # derivation that provides it. The order here is the order the
  # dispatch shim's own `case` tries them in (irrelevant: the names
  # are disjoint).
  toolchains = {
    "leanprover/lean4:v4.29.0" = lean4290;
    "leanprover/lean4:v4.33.1" = lean4331;
    "leanprover/lean4:v4.35.0" = lean4350;
  };

  leanDispatchScript =
    name:
    pkgs.writeShellScriptBin name ''
      set -e
      # No default toolchain: a project without a `lean-toolchain` file, or
      # one that names a version this image does not install, is refused, so
      # no project is ever built with a compiler it did not ask for.
      dir="$PWD"
      while [ "$dir" != "/" ] && [ ! -f "$dir/lean-toolchain" ]; do
        dir="$(dirname "$dir")"
      done
      if [ ! -f "$dir/lean-toolchain" ]; then
        echo "${name}: no lean-toolchain file in $PWD or any parent directory" >&2
        exit 2
      fi
      toolchain="$(tr -d '[:space:]' < "$dir/lean-toolchain")"
      case "$toolchain" in
        ${lib.concatStringsSep "\n        " (
          lib.mapAttrsToList (
            toolchain: drv: "${toolchain}) exec ${drv}/bin/${name} \"$@\" ;;"
          ) toolchains
        )}
        *)
          echo "${name}: $dir/lean-toolchain names '$toolchain'; this image installs leanprover/lean4:v4.29.0, leanprover/lean4:v4.33.1 and leanprover/lean4:v4.35.0 only" >&2
          exit 2
          ;;
      esac
    '';
  leanDispatch = pkgs.symlinkJoin {
    name = "lean4-dispatch";
    paths = map leanDispatchScript [ "lean" "lake" "leanc" "lean4checker" ];
  };
in
{
  inherit lean4290 lean4331 lean4350 toolchains leanDispatch;
}
