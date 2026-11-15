;; Statement-only formalization of miniF2F corpus artifact mathd_algebra_76:
;; an integer-valued function on the integers, equal to n^2 on odd inputs and
;; n^2 - 4*n - 1 on even inputs, has value -1 at 4. This file contains no
;; proof.

(in-package "ACL2")

(defstub mathd-algebra-76-f (n) t)

(defun-sk mathd-algebra-76-integer-valued-p ()
  (forall (n)
    (implies (integerp n)
             (integerp (mathd-algebra-76-f n)))))

(defun-sk mathd-algebra-76-odd-law-p ()
  (forall (n)
    (implies
     (and (integerp n)
          (equal (mod n 2) 1))
     (equal (mathd-algebra-76-f n)
            (expt n 2)))))

(defun-sk mathd-algebra-76-even-law-p ()
  (forall (n)
    (implies
     (and (integerp n)
          (equal (mod n 2) 0))
     (equal (mathd-algebra-76-f n)
            (- (- (expt n 2)
                  (* 4 n))
               1)))))

(defun mathd-algebra-76-statement ()
  (implies
   (and (mathd-algebra-76-integer-valued-p)
        (mathd-algebra-76-odd-law-p)
        (mathd-algebra-76-even-law-p))
   (equal (mathd-algebra-76-f 4) -1)))

(value-triple :itpeval-statement-checked)
:q
