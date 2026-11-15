;; Statement-only formalization of PutnamBench corpus artifact
;; putnam_1966_a4: the closed form for the ascending sequence of positive
;; integers that are not perfect squares, using the nearest integer to the
;; square root of the index. This file contains no proof.

(in-package "ACL2")

;; Searching down from X keeps the source existential square witness internal.
;; For nonnegative X, any integer M with M^2 = X has |M| <= X, so this search
;; is equivalent to existence of an integer square root.
(defun putnam-1966-a4-square-witness-down-p (x candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (equal x 0)
    (or (equal (* candidate candidate) x)
        (putnam-1966-a4-square-witness-down-p
         x (- candidate 1)))))

(defun putnam-1966-a4-perfect-square-p (x)
  (and (natp x)
       (putnam-1966-a4-square-witness-down-p x x)))

;; The source assumptions uniquely determine A on all positive indices.
;; Defining that sequence recursively therefore eliminates the arbitrary
;; function bidirectionally: every source A agrees with this function for
;; n >= 1, and this function itself satisfies the source base and recurrence.
(defun putnam-1966-a4-sequence-value (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (<= n 1))
      2
    (let ((previous
           (putnam-1966-a4-sequence-value (- n 1))))
      (if (putnam-1966-a4-perfect-square-p
           (+ previous 1))
          (+ previous 2)
        (+ previous 1)))))

;; This returns floor(sqrt(N)) for natural N.
(defun putnam-1966-a4-floor-sqrt-down (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      0
    (if (<= (* candidate candidate) n)
        candidate
      (putnam-1966-a4-floor-sqrt-down
       n (- candidate 1)))))

(defun putnam-1966-a4-floor-sqrt (n)
  (putnam-1966-a4-floor-sqrt-down n n))

;; If K = floor(sqrt(N)), comparison of 4*N with (2*K+1)^2 decides whether
;; sqrt(N) lies below or above K+1/2. Equality cannot occur for integral N,
;; so this is exactly round(sqrt(N)), equivalently floor(sqrt(N)+1/2).
(defun putnam-1966-a4-rounded-sqrt (n)
  (let* ((k (putnam-1966-a4-floor-sqrt n))
         (midpoint-numerator (+ (* 2 k) 1)))
    (if (< (* 4 n)
           (* midpoint-numerator midpoint-numerator))
        k
      (+ k 1))))

(defun putnambench-putnam-1966-a4-statement (n)
  (implies
   (and (natp n)
        (<= 1 n))
   (equal
    (putnam-1966-a4-sequence-value n)
    (+ n (putnam-1966-a4-rounded-sqrt n)))))

(value-triple :itpeval-statement-checked)
:q
