# Software Foundations, SNU 4190.574, 2019 Fall

- Instructor: Prof. [Chung-Kil Hur](http://sf.snu.ac.kr/gil.hur)
    + Email address: gil.hur@sf.snu.ac.kr
    + Office: 302-426
- TA: [Juneyoung Lee](http://sf.snu.ac.kr/juneyoung.lee)
    + Email address: juneyoung.lee@sf.snu.ac.kr
    + Office: 302-312-2
- Class material: http://www.cis.upenn.edu/~bcpierce/sf/current/index.html
- Please use email to ask questions (Don't use GitHub Issues)

### Grading

- Exams: 50% (mid-term 20% and final 30%)
- Assignments: 45%
- Attendance: 5%

### Announcement

- Nov. 21: Assignment 4 is uploaded.
- Nov. 19: Final exam will be held on Dec. ~14th Sat~ 17th Tue, 7 - 12 pm at 302동 소프트웨어실습실 (https://cse.snu.ac.kr/facility/소프트웨어-실험실 ). If it conflicts with your schedule, please send a mail to TA.
- Nov. 18: We don't have a class on Thursday (Nov. 21).
- Nov. 12: See [SearchTreeCorrectness.v](SearchTreeCorrectness.v) for the statement and proof of correctness of a search tree.
- Nov. 9: Assignment 3 is uploaded.
- Oct. 31: See [Perm_automation.v](Perm_automation.v) for the shorter proof which is explained at the class
- Oct. 12: Assignment 2 is uploaded.
- Oct. 8: Midterm will be held on Oct. 26th Sat, 7 - 11 pm at 302동 소프트웨어실습실 (https://cse.snu.ac.kr/facility/소프트웨어-실험실 ).
- Sep. 28: Assignment 1 is uploaded.

### Assignments

- Visit http://147.46.242.54:8000 and log-in with your id (e.g. 2016-12345). Your initial password is equivalent to your id.

| Due        	| Description                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|
|------------	|-----------------------------------------------------------------------------------
| Oct.6 23:59  	| Assignment 1                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|
| Oct.20 23:59 	| Assignment 2                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|
| Nov.24 23:59 	| Assignment 3                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|
| Dec.08 23:59 	| Assignment 4                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|


### Coq

- Install Coq [8.9.1](https://coq.inria.fr).
    + Using an installer (Windows, MacOS)
        * Download [Binaries](https://coq.inria.fr/download) and install it.

    + Using OPAM (Linux / MacOS)
        * OPAM is OCaml package manager, and you can use it to install Coq in Linux.
        * See [https://coq.inria.fr/opam/www/using.html](https://coq.inria.fr/opam/www/using.html).

    + Using brew (MacOS)
        * Run `brew install coq`, which will automatically install coq-8.9.1
        * Note this wouldn't install CoqIDE.

- Install IDE for Coq.
    + CoqIDE: installed by default.
        * If you see "Error: The file .. contains library Top.D and not library D.", please open the file with command `coqide -R . Top D.v`. 
    + Emacs: [Company-Coq](https://github.com/cpitclaudel/company-coq). Follow the setup instructions.
        * If it shows `Searching for program No such file or directory coqtop` error, please add `(custom-set-variables '(coq-prog-name "PATH/TO/coqtop"))` to `.emacs` file.
        * In case of MacOS, coqtop is at `/Applications/CoqIDE_8.9.1.app/Contents/Resources/bin/`.
    + Visual Studio Code: Install VSCoq
