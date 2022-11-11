{
  description = "Dev shell for coq";
  
  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs supportedSystems (system: f system);
      nixpkgsFor = forAllSystems (system: import nixpkgs {
        inherit system;
      });
    in
    {
      packages = forAllSystems (system: {
        coq_lessons = nixpkgsFor.${system}.stdenv.mkDerivation { 
            pname = "coq_lessons"; 
            version = "dev";
            buildCommand = ''
              mkdir $out
              cp -r ${nixpkgsFor.${system}.coqPackages.mathcomp} $out/mathcomp
              ${nixpkgsFor.${system}.coq}/bin/coqc -v > $out/ver
              
            ''; 
            inherit system;
        };
      });

      defaultPackage = forAllSystems (system: self.packages.${system}.coq_lessons);
      
      devShell = forAllSystems (system: nixpkgsFor.${system}.mkShell {
        buildInputs = 
          with nixpkgsFor.${system}; [ 
            coq
            coqPackages.mathcomp
            coqPackages.QuickChick 
          ];
        shellHook = ''
          export PS1='\e[1;34mdev > \e[0m'
        '';
      });
    };
}
