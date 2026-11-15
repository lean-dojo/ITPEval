;; Statement-only formalization of PutnamBench corpus artifact putnam_1995_a3:
;; two successive nine-digit replacement relations force every corresponding
;; first-and-third digit difference to be divisible by 7. This file contains
;; no proof.

(in-package "ACL2")

;; A nine-element integer list is exactly a function Fin 9 -> Z, represented
;; by its values at indices 0 through 8. The source definitions uniquely
;; determine DIGITS_TO_NUM and RELATION, so substituting the definitions below
;; is bidirectionally equivalent to quantifying over those defined symbols.

(defun putnam-1995-a3-decimal-digit-list-p (digits)
  (if (consp digits)
      (and
       (integerp (car digits))
       (<= 0 (car digits))
       (< (car digits) 10)
       (putnam-1995-a3-decimal-digit-list-p (cdr digits)))
    (equal digits nil)))

(defun putnam-1995-a3-digit-vector-p (digits)
  (and
   (true-listp digits)
   (equal (len digits) 9)
   (putnam-1995-a3-decimal-digit-list-p digits)))

(defun putnam-1995-a3-digits-to-num (digits)
  (+ (nth 0 digits)
     (* (nth 1 digits) 10)
     (* (nth 2 digits) (expt 10 2))
     (* (nth 3 digits) (expt 10 3))
     (* (nth 4 digits) (expt 10 4))
     (* (nth 5 digits) (expt 10 5))
     (* (nth 6 digits) (expt 10 6))
     (* (nth 7 digits) (expt 10 7))
     (* (nth 8 digits) (expt 10 8))))

(defun putnam-1995-a3-replacement-divisible-p
    (digits replacements index)
  (equal
   (mod
    (putnam-1995-a3-digits-to-num
     (update-nth
      index
      (nth index replacements)
      digits))
    7)
   0))

(defun putnam-1995-a3-relation-p (digits replacements)
  (and
   (putnam-1995-a3-digit-vector-p digits)
   (putnam-1995-a3-digit-vector-p replacements)
   (putnam-1995-a3-replacement-divisible-p digits replacements 0)
   (putnam-1995-a3-replacement-divisible-p digits replacements 1)
   (putnam-1995-a3-replacement-divisible-p digits replacements 2)
   (putnam-1995-a3-replacement-divisible-p digits replacements 3)
   (putnam-1995-a3-replacement-divisible-p digits replacements 4)
   (putnam-1995-a3-replacement-divisible-p digits replacements 5)
   (putnam-1995-a3-replacement-divisible-p digits replacements 6)
   (putnam-1995-a3-replacement-divisible-p digits replacements 7)
   (putnam-1995-a3-replacement-divisible-p digits replacements 8)))

(defun putnam-1995-a3-all-differences-divisible-p (first third)
  (and
   (equal (mod (- (nth 0 first) (nth 0 third)) 7) 0)
   (equal (mod (- (nth 1 first) (nth 1 third)) 7) 0)
   (equal (mod (- (nth 2 first) (nth 2 third)) 7) 0)
   (equal (mod (- (nth 3 first) (nth 3 third)) 7) 0)
   (equal (mod (- (nth 4 first) (nth 4 third)) 7) 0)
   (equal (mod (- (nth 5 first) (nth 5 third)) 7) 0)
   (equal (mod (- (nth 6 first) (nth 6 third)) 7) 0)
   (equal (mod (- (nth 7 first) (nth 7 third)) 7) 0)
   (equal (mod (- (nth 8 first) (nth 8 third)) 7) 0)))

(defun putnambench-putnam-1995-a3-statement (d e f)
  (implies
   (and
    (putnam-1995-a3-relation-p d e)
    (putnam-1995-a3-relation-p e f))
   (putnam-1995-a3-all-differences-divisible-p d f)))

(value-triple :itpeval-statement-checked)
:q
