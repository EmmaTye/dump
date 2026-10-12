{
  description = "Brain dump";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let 
      pkgs = nixpkgs.legacyPackages.${system};
      agda = pkgs.agda.withPackages (ps: with ps; [
        standard-library
        agda-categories
      ]);
    in {
      formatter = pkgs.nixpkgs-fmt;

      devShell = pkgs.mkShell {
        buildInputs = with pkgs; [
          # Idris build deps
          gnumake
          gcc
          coreutils
          gmp
          chez
          # Agda
          agda
          # Isabelle
          isabelle
          # Haskell
          cabal-install
          haskell-language-server
          ghc
        ];

        shellHook = ''
          export PATH="$HOME/.pack/bin:$PATH"
        '';
      };
    });
}

