{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; config.allowUnfree = true; };
    in
    {
      devShell = pkgs.mkShell {
        buildInputs = with pkgs; [
          gnumake
          ocaml
          rocq-core
          rocqPackages.stdlib
          #coq
          #coqPackages.stdlib
          rocqPackages.vsrocq-language-server
          coqPackages.coq-lsp
        ];
      };
    }
  );
}
