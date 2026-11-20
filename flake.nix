{
  description = "Categories with families in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    # The development needs `Cubical.Data.IterativeSets.*` from cubical master
    # (2026-11). To use another revision of cubical, change the hash here.
    cubical = {
      url = "github:agda/cubical/8f0a71b3b3c2435cd1f579328314ae10233b1308";
      flake = false;
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      cubical,
    }:
    let
      inherit (nixpkgs) lib;
      forAllSystems = lib.genAttrs [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ];
      pkgsFor = system: nixpkgs.legacyPackages.${system};

      # The cubical library at the pinned revision.
      cubicalFor =
        system:
        (pkgsFor system).agdaPackages.cubical.overrideAttrs {
          version = "0.9-unstable-${cubical.lastModifiedDate}";
          src = cubical;
        };
    in
    {
      packages = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
        in
        {
          # Typechecks every module of the library (`agda --build-library`).
          default = pkgs.agdaPackages.mkDerivation {
            pname = "fun-with-cwf";
            version = "0-unstable-${self.lastModifiedDate or "dirty"}";
            src = lib.fileset.toSource {
              root = ./.;
              fileset = lib.fileset.unions [
                ./funwithcwf.agda-lib
                (lib.fileset.fileFilter (file: file.hasExt "agda") ./.)
              ];
            };
            libraryName = "FunWithCwf";
            libraryFile = "funwithcwf.agda-lib";
            buildInputs = [ (cubicalFor system) ];
            meta = {
              description = "Categories with families in Cubical Agda";
              platforms = lib.platforms.unix;
            };
          };
        }
      );

      checks = forAllSystems (system: {
        build = self.packages.${system}.default;
      });

      devShells = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
        in
        {
          default = pkgs.mkShell {
            packages = [ (pkgs.agdaPackages.agda.withPackages [ (cubicalFor system) ]) ];
          };
        }
      );

      formatter = forAllSystems (system: (pkgsFor system).nixfmt);
    };
}
