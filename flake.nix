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
        overlays = [ self.overlay ];
      });
    in
    {
      packages = forAllSystems (system: {
         coq_lessons = nixpkgsFor.${system}.coq_lessons;
      });
      defaultPackage = forAllSystems (system: self.packages.${system}.coq_lessons);
      
      # devShells.default = forAllSystems (system: nixpkgs.mkShell {
      #   nativeBuildInputs = [ 
      #     pkgs.coq
      #     pkgs.coqPackages.mathcomp
      #     pkgs.coqPackages.QuickChick 
      #   ];
      # });
    };
}
