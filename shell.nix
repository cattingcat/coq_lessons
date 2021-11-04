{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    # nativeBuildInputs is usually what you want -- tools you need to run
    nativeBuildInputs = [ 
	pkgs.coq
	pkgs.coqPackages.mathcomp
	pkgs.coqPackages.HTT
	pkgs.coqPackages.QuickChick ];
}

