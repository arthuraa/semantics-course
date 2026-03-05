{
  description = "MPI semantics course";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    stdpp.url = "git+https://gitlab.mpi-sws.org/iris/stdpp.git";
    stdpp.flake = false;
    iris.url = "git+https://gitlab.mpi-sws.org/iris/iris.git";
    iris.flake = false;
    nix-github-actions.url = "github:nix-community/nix-github-actions";
    nix-github-actions.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs@{ self, flake-parts, stdpp, iris, nixpkgs, nix-github-actions, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import a flake module
        # 1. Add foo to inputs
        # 2. Add foo as a parameter to the outputs function
        # 3. Add here: foo.flakeModule

      ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        # Per-system attributes can be defined here. The self' and inputs'
        # module parameters provide easy access to attributes of the same
        # system.

        _module.args.pkgs = import self.inputs.nixpkgs {
          inherit system;
          overlays = [
            self.overlays.default
          ];
          config = { };
        };

        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
          ];
          inputsFrom = [
            pkgs.coqPackages.semantics-course
          ];
        };

        packages.default = pkgs.coqPackages.semantics-course;

        checks.default = self'.packages.default;

      };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

        githubActions = nix-github-actions.lib.mkGithubMatrix {
          checks = nixpkgs.lib.getAttrs [ "x86_64-linux" "aarch64-darwin" ] self.checks;
        };

        overlays.default = final: prev: {
          coqPackages = prev.coqPackages.overrideScope (final': prev': {
            stdpp = prev'.lib.overrideCoqDerivation {
              defaultVersion = "dev";
              release.dev.src = stdpp;
            } prev'.stdpp;
            iris = prev'.lib.overrideCoqDerivation {
              defaultVersion = "dev";
              release.dev.src = iris;
            } prev'.iris;
            semantics-course = prev'.mkCoqDerivation {
              pname = "semantics-course";
              defaultVersion = "dev";
              release.dev.src = ./.;
              propagatedBuildInputs = [
                final.rocq-core
                final.rocqPackages.stdlib
                final.coqPackages.iris
                final.coqPackages.stdpp
                final.coqPackages.autosubst
                final.coqPackages.equations
              ];
            };
          });
        };

      };
    };
}
