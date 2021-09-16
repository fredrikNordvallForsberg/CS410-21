# Installing Agda on Windows 10

This short guide will help you get Agda 2.6.2 running on a Windows 10 machine.

1\. Get the [Haskell Platform](https://www.haskell.org/platform/windows.html) and follow the instructions. You can use the minimal installer for this class. Note that you will need an administrave PowerShell prompt when installing Chocolatey.

2\. Run 
``` 
cabal update
cabal install alex happy Agda
```
This will compile Agda on your machine. The process might take very long time (> 30 minutes) and is quite memory intensive (make sure you have at least 4GB free). 

3\. Install emacs. You can get a Windows installer from [here](https://ftp.gnu.org/gnu/emacs/windows/emacs-27/).

4\. Create `%appdata%\.emacs` and paste the following:
```
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))
```
(`%appdata%` usually expands to `C:\Users\<your username>\AppData\Roaming`).

5\. Get the [agda standard library](https://github.com/agda/agda-stdlib/archive/v1.7.zip). Unzip it to a destination of your choice, call that parent directory `$DIR`.

6\. Create `%appdata%\agda\libraries` and add the following line to it, replacing `$DIR` with the concrete path:
```
$DIR\agda-stdlib-1.7\standard-library.agda-lib
```

7\. (OPTIONAL) Create `%appdata%\agda\defaults` and add the following line to it:
```
standard-library
```
This means that all your files will know about the standard library by default. (The coursework, however, explicitly depends on the standard library, so it doesn't rely on this step.)

8\. Now you are ready to start working on your first coursework :slightly_smiling_face:. Good luck!
