{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs =
    { nixpkgs, ... }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };

    in
    {
      devShells.${system} = {
        default = pkgs.mkShell {
          packages = with pkgs; [
            (agda.withPackages (
              apkgs: with apkgs; [
                (cubical.overrideAttrs {
                  src = pkgs.fetchFromGitHub {
                    owner = "agda";
                    repo = "cubical";
                    rev = "8f0a71b3b3c2435cd1f579328314ae10233b1308";
                    hash = "sha256-BPd/C4pt2siRB/cLU4tijf/MfgDiSNOhdiZiYAG/PN4=";
                  };
                })
              ]
            ))
          ];
        };
      };
    };
}
