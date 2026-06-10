{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs = {nixpkgs, ...}: let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };

  in {
    devShells.${system} = {
      default = pkgs.mkShell {
        packages = with pkgs; [
          (agda.withPackages (apkgs: with apkgs; [
            (cubical.overrideAttrs {
              src = pkgs.fetchFromGitHub {
                owner = "agda";
                repo = "cubical";
                rev = "d4a2af62de40a6ca9a0b51981e41f804d879a1b9";
                hash = "sha256-eNslweY02wanasdsIVw3icuyQlKx5U6rbMKG5NTHFTY=";
              };})
          ]))
        ];
      };
    };
  };
}
