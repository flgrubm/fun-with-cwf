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
                    rev = "6e6df4e74d4b03205c942c1574c6fea0b2cc213e";
                    hash = "sha256-j06MMU8IVK63Rc6JiUlJWr7RvTipvKq094voALqbijE=";
                  };
                })
              ]
            ))
          ];
        };
      };
    };
}
