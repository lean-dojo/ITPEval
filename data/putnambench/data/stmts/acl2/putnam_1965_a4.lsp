;; Statement-only formalization of PutnamBench artifact putnam_1965_a4:
;; a finite nonempty bipartite dance relation with no boy adjacent to every
;; girl but every girl adjacent to some boy has a crossed pair. This file
;; contains no proof.

(in-package "ACL2")

;; GIRLS and BOYS are duplicate-free enumerations of the arbitrary finite
;; source types. DANCES is an ACL2 function object evaluated by APPLY$, so the
;; relation is not replaced by a fixed table. Recursion over the complete
;; carriers is exactly the source's finite universal and existential
;; quantification.

(defun putnam-1965-a4-dances-p (dances girl boy)
  (if (apply$ dances (list girl boy))
      t
    nil))

(defun putnam-1965-a4-boy-dances-with-every-girl-p
    (boy girls dances)
  (if (consp girls)
      (and
       (putnam-1965-a4-dances-p dances (car girls) boy)
       (putnam-1965-a4-boy-dances-with-every-girl-p
        boy (cdr girls) dances))
    t))

(defun putnam-1965-a4-some-boy-dances-with-every-girl-p
    (boys girls dances)
  (if (consp boys)
      (or
       (putnam-1965-a4-boy-dances-with-every-girl-p
        (car boys) girls dances)
       (putnam-1965-a4-some-boy-dances-with-every-girl-p
        (cdr boys) girls dances))
    nil))

(defun putnam-1965-a4-girl-dances-with-some-boy-p
    (girl boys dances)
  (if (consp boys)
      (or
       (putnam-1965-a4-dances-p dances girl (car boys))
       (putnam-1965-a4-girl-dances-with-some-boy-p
        girl (cdr boys) dances))
    nil))

(defun putnam-1965-a4-every-girl-dances-with-some-boy-p
    (girls boys dances)
  (if (consp girls)
      (and
       (putnam-1965-a4-girl-dances-with-some-boy-p
        (car girls) boys dances)
       (putnam-1965-a4-every-girl-dances-with-some-boy-p
        (cdr girls) boys dances))
    t))

(defun putnam-1965-a4-some-second-boy-crosses-p
    (girl other-girl first-boy boys dances)
  (if (consp boys)
      (or
       (and
        (putnam-1965-a4-dances-p
         dances other-girl (car boys))
        (not
         (putnam-1965-a4-dances-p
          dances girl (car boys)))
        (putnam-1965-a4-dances-p
         dances girl first-boy)
        (not
         (putnam-1965-a4-dances-p
          dances other-girl first-boy)))
       (putnam-1965-a4-some-second-boy-crosses-p
        girl other-girl first-boy (cdr boys) dances))
    nil))

(defun putnam-1965-a4-some-boy-pair-crosses-p
    (girl other-girl remaining-boys boys dances)
  (if (consp remaining-boys)
      (or
       (putnam-1965-a4-some-second-boy-crosses-p
        girl other-girl (car remaining-boys) boys dances)
       (putnam-1965-a4-some-boy-pair-crosses-p
        girl other-girl (cdr remaining-boys) boys dances))
    nil))

(defun putnam-1965-a4-some-second-girl-crosses-p
    (girl remaining-girls boys dances)
  (if (consp remaining-girls)
      (or
       (putnam-1965-a4-some-boy-pair-crosses-p
        girl (car remaining-girls) boys boys dances)
       (putnam-1965-a4-some-second-girl-crosses-p
        girl (cdr remaining-girls) boys dances))
    nil))

(defun putnam-1965-a4-crossed-pair-exists-p
    (remaining-girls girls boys dances)
  (if (consp remaining-girls)
      (or
       (putnam-1965-a4-some-second-girl-crosses-p
        (car remaining-girls) girls boys dances)
       (putnam-1965-a4-crossed-pair-exists-p
        (cdr remaining-girls) girls boys dances))
    nil))

(defun putnambench-putnam-1965-a4-statement
    (girls boys dances)
  (implies
   (and
    (true-listp girls)
    (consp girls)
    (no-duplicatesp-equal girls)
    (true-listp boys)
    (consp boys)
    (no-duplicatesp-equal boys)
    (not
     (putnam-1965-a4-some-boy-dances-with-every-girl-p
      boys girls dances))
    (putnam-1965-a4-every-girl-dances-with-some-boy-p
     girls boys dances))
   (putnam-1965-a4-crossed-pair-exists-p
    girls girls boys dances)))

(value-triple :itpeval-statement-checked)
:q
