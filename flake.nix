{
  description = "Dev shell for coq";
  
  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs supportedSystems (system: f system);
      nixpkgsFor = forAllSystems (system: import nixpkgs {
        inherit system;
      });
    in
    {
      packages = forAllSystems (system: {
        coq_lessons = derivation { 
            name = "coq_lessons"; 
            builder = ''
              ${nixpkgsFor.${system}.coq}/bin/coqc -v
            ''; 
            inherit system;
        };
      });

      defaultPackage = forAllSystems (system: self.packages.${system}.coq_lessons);
      
      devShells.default = forAllSystems (system: nixpkgs.mkShell {
        nativeBuildInputs = [ 
          nixpkgsFor.${system}.coq
          nixpkgsFor.${system}.coqPackages.mathcomp
          nixpkgsFor.${system}.coqPackages.QuickChick 
        ];
      });
    };
}
