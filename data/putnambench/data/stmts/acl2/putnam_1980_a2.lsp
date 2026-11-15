;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_a2:
;; the number of ordered positive-integer quadruples whose four triple least
;; common multiples all equal 3^r*7^s is
;; (1+4*r+6*r^2)*(1+4*s+6*s^2). This file contains no proof.

(in-package "ACL2")

(defun putnam-1980-a2-gcd-search (left right candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      1
    (if (and (equal (mod left candidate) 0)
             (equal (mod right candidate) 0))
        candidate
      (putnam-1980-a2-gcd-search
       left right (- candidate 1)))))

(defun putnam-1980-a2-gcd (left right)
  (putnam-1980-a2-gcd-search
   left right (if (< left right) left right)))

(defun putnam-1980-a2-lcm (left right)
  (/ (* left right)
     (putnam-1980-a2-gcd left right)))

(defun putnam-1980-a2-triple-lcm (x y z)
  (putnam-1980-a2-lcm
   (putnam-1980-a2-lcm x y)
   z))

(defun putnam-1980-a2-admissible-p (common-lcm a b c d)
  (and
   (natp common-lcm)
   (< 0 common-lcm)
   (natp a)
   (< 0 a)
   (natp b)
   (< 0 b)
   (natp c)
   (< 0 c)
   (natp d)
   (< 0 d)
   (equal common-lcm
          (putnam-1980-a2-triple-lcm a b c))
   (equal common-lcm
          (putnam-1980-a2-triple-lcm a b d))
   (equal common-lcm
          (putnam-1980-a2-triple-lcm a c d))
   (equal common-lcm
          (putnam-1980-a2-triple-lcm b c d))))

;; If a positive quadruple is admissible, each coordinate occurs in a triple
;; with LCM COMMON-LCM, hence divides and is at most COMMON-LCM. The nested
;; recursions therefore count exactly the full source set, not a bounded
;; approximation.

(defun putnam-1980-a2-count-d
    (common-lcm a b c d-limit)
  (declare (xargs :measure (nfix d-limit)))
  (if (zp d-limit)
      0
    (+
     (if (putnam-1980-a2-admissible-p
          common-lcm a b c d-limit)
         1
       0)
     (putnam-1980-a2-count-d
      common-lcm a b c (- d-limit 1)))))

(defun putnam-1980-a2-count-c
    (common-lcm a b c-limit)
  (declare (xargs :measure (nfix c-limit)))
  (if (zp c-limit)
      0
    (+
     (putnam-1980-a2-count-d
      common-lcm a b c-limit common-lcm)
     (putnam-1980-a2-count-c
      common-lcm a b (- c-limit 1)))))

(defun putnam-1980-a2-count-b
    (common-lcm a b-limit)
  (declare (xargs :measure (nfix b-limit)))
  (if (zp b-limit)
      0
    (+
     (putnam-1980-a2-count-c
      common-lcm a b-limit common-lcm)
     (putnam-1980-a2-count-b
      common-lcm a (- b-limit 1)))))

(defun putnam-1980-a2-count-a
    (common-lcm a-limit)
  (declare (xargs :measure (nfix a-limit)))
  (if (zp a-limit)
      0
    (+
     (putnam-1980-a2-count-b
      common-lcm a-limit common-lcm)
     (putnam-1980-a2-count-a
      common-lcm (- a-limit 1)))))

(defun putnam-1980-a2-quadruple-count (common-lcm)
  (if (natp common-lcm)
      (putnam-1980-a2-count-a common-lcm common-lcm)
    0))

(defun putnam-1980-a2-solution (r s)
  (*
   (+ 1 (* 4 r) (* 6 r r))
   (+ 1 (* 4 s) (* 6 s s))))

(defun putnambench-putnam-1980-a2-statement (r s)
  (implies
   (and
    (natp r)
    (< 0 r)
    (natp s)
    (< 0 s))
   (let ((common-lcm
          (* (expt 3 r)
             (expt 7 s))))
     (equal
      (putnam-1980-a2-quadruple-count common-lcm)
      (putnam-1980-a2-solution r s)))))

(value-triple :itpeval-statement-checked)
:q
