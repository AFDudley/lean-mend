/*
  Local derivations for the gate tools whose version must match the
  Dockerfile gate image (.exophial/gate/Dockerfile) exactly, for parity
  (D10, docs/plans/nix-images.md). A version change is a local
  `overridePythonAttrs` on the one package that needs it, never a
  nixpkgs-wide overlay (D9) -- so no unrelated package rebuilds.

  Byte-identical construction to armada-lean's own nix/pins.nix (the
  same pinned upstream revs), so the two repos share these store paths
  rather than each building a second copy.
*/
{ pkgs }:
let
  # pre-commit-hooks 4.6.0: the 7 console scripts the converted local
  # hooks in .pre-commit-config.yaml call directly (trailing-whitespace-
  # fixer, end-of-file-fixer, check-yaml, check-added-large-files,
  # check-merge-conflict, check-case-conflict, mixed-line-ending).
  preCommitHooks = pkgs.python3Packages.pre-commit-hooks.overridePythonAttrs (_old: {
    version = "4.6.0";
    src = pkgs.fetchFromGitHub {
      owner = "pre-commit";
      repo = "pre-commit-hooks";
      tag = "v4.6.0";
      hash = "sha256-p/pPpuuNjVxHSPyi4RL2DJlj9weSq8QinugQ4zmv9Ck=";
    };
    doCheck = false;
    nativeCheckInputs = [ ];
    preCheck = "";
  });
in
{
  inherit preCommitHooks;
}
