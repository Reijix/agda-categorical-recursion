{ pkgs ? import <nixpkgs> { } }:
with pkgs;
mkShell {
  buildInputs = [ 
    (agda.withPackages (
      let stdlib = (agdaPackages.standard-library.overrideAttrs (oldAttrs: {
        version = "2.0";
        src = fetchFromGitHub {
          repo = "agda-stdlib";
          owner = "agda";
          rev = "v2.0";
          hash = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
        };
      })); in [
        stdlib
        (agdaPackages.agda-categories.overrideAttrs (oldAttrs : {
          version = "0.2.0";
          src = fetchFromGitHub {
            repo = "agda-categories";
            owner = "agda";
            rev = "81d03d50386daea841dbd07db0ab85792c79f38a";
            hash = "sha256-0Y2sfcZeMxIZdyzDsLcQwNIC7l6gW/I0ir6HVToDLwY=";
          };
          # without this nix might use a wrong version of the stdlib to try and typecheck agda-categories
          buildInputs = [ (agda.withPackages [ stdlib ]) ];
          GHCRTS = "-M6G";
        }))
      ])
    ) 
  ];

  shellHook = ''
    # ...
  '';
}

