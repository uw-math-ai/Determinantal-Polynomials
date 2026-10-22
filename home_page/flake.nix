{
  description = "Ruby + Bundler for building the Jekyll home page (`nix develop`)";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          # Ruby 3.4 matches CI (`ruby-version` in .github/workflows/blueprint.yml).
          # pkg-config + openssl + libyaml let Bundler compile the gems' native extensions.
          packages = [ pkgs.ruby_3_4 pkgs.pkg-config pkgs.openssl pkgs.libyaml ];
          # Install gems into ./vendor/bundle instead of a global directory.
          BUNDLE_PATH = "vendor/bundle";
        };
      });
    };
}
