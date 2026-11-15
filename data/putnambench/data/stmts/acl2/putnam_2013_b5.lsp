;; Statement-only formalization of PutnamBench corpus artifact putnam_2013_b5:
;; the exact count of endofunctions on {1,...,n} whose every orbit eventually
;; reaches {1,...,k}. This file contains no proof.

(in-package "ACL2")

;; For positive N, CODE in 0,...,N^N-1 is the base-N image table of a unique
;; function {1,...,N} -> {1,...,N}; the digit at position X-1, shifted by one,
;; is the value at X. Thus the exhaustive count below ranges bijectively over
;; the source function space rather than restricting it.
(defun putnam-2013-b5-function-value (code n x)
  (+ 1
     (mod (floor code (expt n (- x 1)))
          n)))

;; On an N-element carrier, an orbit that does not enter {1,...,K} among its
;; first N+1 vertices has repeated a vertex entirely above K and can never
;; enter that set. Hence this bounded search is equivalent to the source's
;; existential quantification over all natural iterate counts.
(defun putnam-2013-b5-orbit-reaches-p
    (code n k current steps)
  (declare (xargs :measure (nfix steps)))
  (or (<= current k)
      (and
       (not (zp steps))
       (putnam-2013-b5-orbit-reaches-p
        code
        n
        k
        (putnam-2013-b5-function-value code n current)
        (- steps 1)))))

(defun putnam-2013-b5-all-orbits-reach-p
    (code n k start-count)
  (declare (xargs :measure (nfix start-count)))
  (if (zp start-count)
      t
    (and
     (putnam-2013-b5-orbit-reaches-p
      code n k start-count n)
     (putnam-2013-b5-all-orbits-reach-p
      code n k (- start-count 1)))))

(defun putnam-2013-b5-count-functions
    (remaining n k)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((code (- remaining 1)))
      (+
       (if (putnam-2013-b5-all-orbits-reach-p
            code n k n)
           1
         0)
       (putnam-2013-b5-count-functions
        code n k)))))

(defun putnambench-putnam-2013-b5-statement (n k)
  (implies
   (and
    (posp n)
    (natp k)
    (<= 1 k)
    (<= k n))
   (equal
    (putnam-2013-b5-count-functions
     (expt n n) n k)
    (* k (expt n (- n 1))))))

(value-triple :itpeval-statement-checked)
:q
