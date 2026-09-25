{
  description = "A startup basic project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
    devshell = {
      url = "github:numtide/devshell";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        inputs.devshell.flakeModule
      ];

      perSystem = { pkgs, ... }: {
        devshells.default = {
          packages = [ pkgs.coq ];

          # nixpkgs ships the Rocq Stdlib but never registers it; derive
          # ROCQPATH from the package's own COQLIBINSTALL flag.
          env = [
            {
              name = "ROCQPATH";
              prefix =
                let
                  std = pkgs.rocqPackages.stdlib;
                  hits = pkgs.lib.filter (pkgs.lib.hasPrefix "COQLIBINSTALL=") std.drvAttrs.installFlags;
                in
                assert pkgs.lib.assertMsg (hits != [ ])
                  "rocqPackages.stdlib: no COQLIBINSTALL= entry in drvAttrs.installFlags";
                builtins.replaceStrings [ "$(out)" ] [ std.outPath ] (
                  pkgs.lib.removePrefix "COQLIBINSTALL=" (builtins.head hits)
                );
            }
          ];
        };
      };

      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];
    };
}
