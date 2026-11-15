;; Statement-only formalization of Hundred Theorems artifact 003,
;; "The Denumerability of the Rational Numbers": explicit Calkin-Wilf maps are
;; mutual inverses between ACL2 rational numbers and natural numbers. This file
;; contains no proof.

(in-package "ACL2")

(defun ht003-cw-encode (p q)
  (declare (xargs :measure (+ (nfix p) (nfix q))))
  (if (and (posp p) (posp q))
      (cond ((equal p q) 1)
            ((< p q)
             (* 2 (ht003-cw-encode p (- q p))))
            (t
             (+ 1 (* 2 (ht003-cw-encode (- p q) q)))))
    1))

(defun ht003-cw-decode-pair (n)
  (declare (xargs :measure (nfix n)))
  (if (and (posp n) (< 1 n))
      (let* ((previous (ht003-cw-decode-pair (- n 1)))
             (p (car previous))
             (q (cdr previous))
             (k (floor p q))
             (next-q (- (* (+ (* 2 k) 1) q) p)))
        (cons q next-q))
    (cons 1 1)))

(defun ht003-positive-index-to-rational (n)
  (let ((pair (ht003-cw-decode-pair n)))
    (/ (car pair) (cdr pair))))

(defun ht003-rational-to-natural (x)
  (if (rationalp x)
      (cond ((equal x 0) 0)
            ((< 0 x)
             (- (* 2
                   (ht003-cw-encode (numerator x) (denominator x)))
                1))
            (t
             (* 2
                (ht003-cw-encode (- (numerator x)) (denominator x)))))
    0))

(defun ht003-natural-to-rational (n)
  (if (natp n)
      (cond ((equal n 0) 0)
            ((equal (mod n 2) 1)
             (ht003-positive-index-to-rational (/ (+ n 1) 2)))
            (t
             (- (ht003-positive-index-to-rational (/ n 2)))))
    0))

(defun hundred-theorems-003-statement (x n)
  (and (implies (rationalp x)
                (and (natp (ht003-rational-to-natural x))
                     (equal
                      (ht003-natural-to-rational
                       (ht003-rational-to-natural x))
                      x)))
       (implies (natp n)
                (and (rationalp (ht003-natural-to-rational n))
                     (equal
                      (ht003-rational-to-natural
                       (ht003-natural-to-rational n))
                      n)))))

(value-triple :itpeval-statement-checked)
:q
