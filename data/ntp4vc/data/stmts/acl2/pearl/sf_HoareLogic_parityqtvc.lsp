;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/sf_HoareLogic_parityqtvc: initialization and preservation of the
;; parity loop invariant over unbounded mathematical integers, with the exit
;; condition characterizing the inductively defined even numbers. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source inductive relation has base 0 and the sole constructor x |-> x+2,
;; so its elements are exactly the nonnegative integers divisible by 2.
(defun sf-parity-even-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (equal (mod value 2) 0)))

;; This is the universally quantified preservation and exit obligation from
;; the source VC. Integer guards preserve the typed quantifier domains.
(defun-sk sf-parity-loop-obligation-p (x)
  (forall
   (y x1)
   (implies
    (and
     (integerp y)
     (integerp x1))
    (implies
     (and
      (<= 0 x1)
      (or
       (and
        (equal y 0)
        (sf-parity-even-p (- x x1)))
       (and
        (equal y 1)
        (sf-parity-even-p (+ (- x x1) 1)))))
     (if
         (not (equal x1 0))
         (and
          (and
           (<= 0 x1)
           (< (- x1 1) x1))
          (<= 0 (- x1 1))
          (or
           (and
            (equal (- 1 y) 0)
            (sf-parity-even-p
             (- x (- x1 1))))
           (and
            (equal (- 1 y) 1)
            (sf-parity-even-p
             (+ (- x (- x1 1)) 1)))))
       (iff
        (equal y 0)
        (sf-parity-even-p x)))))))

(defun ntp4vc-sf-hoarelogic-parityqtvc-statement (x)
  (implies
   (and
    (integerp x)
    (<= 0 x))
   (and
    (<= 0 x)
    (or
     (sf-parity-even-p (- x x))
     (and
      (equal 0 1)
      (sf-parity-even-p (+ (- x x) 1))))
    (sf-parity-loop-obligation-p x))))

(value-triple :itpeval-statement-checked)
:q
