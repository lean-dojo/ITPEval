;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_b2:
;; the product of the first n positive odd integers lies between the stated
;; consecutive half-integer powers involving Euler's number. This file
;; contains no proof.

(in-package "ACL2")

;; The source product 1*3*...*(2*n-1).
(defun putnam-1996-b2-odd-product (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* (- (* 2 n) 1)
       (putnam-1996-b2-odd-product (- n 1)))))

(defun putnam-1996-b2-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-1996-b2-factorial (- n 1)))))

;; For natural K, this exact rational prefix is
;;   sum_(j < TERMS) K^j/j!,
;; and increases to exp(K).
(defun putnam-1996-b2-exp-lower (k terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      0
    (let ((degree (- terms 1)))
      (+ (putnam-1996-b2-exp-lower k degree)
         (/ (expt k degree)
            (putnam-1996-b2-factorial degree))))))

;; When TERMS > K, the omitted Taylor tail begins with K^TERMS/TERMS!,
;; and successive-term ratios are at most K/(TERMS+1). Thus this is an
;; exact rational upper enclosure for exp(K), converging to exp(K).
(defun putnam-1996-b2-exp-upper (k terms)
  (if (and (natp k)
           (natp terms)
           (< k terms))
      (+ (putnam-1996-b2-exp-lower k terms)
         (* (/ (expt k terms)
               (putnam-1996-b2-factorial terms))
            (/ (+ terms 1)
               (- (+ terms 1) k))))
    0))

;; Put M=2*N-1, U=2*N+1, and P=1*3*...*M. Positivity makes the two
;; source inequalities equivalent, after squaring, to
;;
;;   M^M < P^2*exp(M)  and  P^2*exp(U) < U^U.
;;
;; For positive integer K, exp(K) is transcendental, so neither comparison
;; can be equality. Consequently the first strict inequality is equivalent
;; to M^M being at most every rational upper enclosure of P^2*exp(M), and
;; the second is equivalent to every rational lower enclosure of P^2*exp(U)
;; being at most U^U. TERMS is therefore a universal precision probe, not an
;; existential witness; ranging over all TERMS > U gives exactly the two
;; source real inequalities.
(defun putnambench-putnam-1996-b2-statement (n terms)
  (implies
   (and (posp n)
        (natp terms)
        (< (+ (* 2 n) 1) terms))
   (let* ((m (- (* 2 n) 1))
          (u (+ (* 2 n) 1))
          (product (putnam-1996-b2-odd-product n))
          (product-squared (* product product)))
     (and
      (<= (expt m m)
          (* product-squared
             (putnam-1996-b2-exp-upper m terms)))
      (<= (* product-squared
             (putnam-1996-b2-exp-lower u terms))
          (expt u u))))))

(value-triple :itpeval-statement-checked)
:q
