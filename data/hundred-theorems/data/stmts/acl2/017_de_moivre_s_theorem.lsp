; Statement-only formalization of hundred-theorems artifact 017,
; "De Moivre's Theorem": for every complex z and natural n,
; (cos z + i sin z)^n = cos(nz) + i sin(nz).  The two sides are entire,
; so universal equality on the full complex plane is equivalent to equality
; of every Taylor coefficient.  This file contains the statement and no proof.

(in-package "ACL2")

(defun ht017-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (ht017-factorial (- n 1)))))

(defun ht017-cosine-coefficient (degree)
  (if (and (natp degree)
           (evenp degree))
      (/ (expt -1 (floor degree 2))
         (ht017-factorial degree))
    0))

(defun ht017-sine-coefficient (degree)
  (if (and (natp degree)
           (oddp degree))
      (/ (expt -1 (floor degree 2))
         (ht017-factorial degree))
    0))

(defun ht017-cos-plus-i-sin-coefficient (degree)
  (+ (ht017-cosine-coefficient degree)
     (* #c(0 1) (ht017-sine-coefficient degree))))

; A number below (degree + 1)^power encodes one power-tuple in base
; (degree + 1).  The following two functions compute its total degree and
; the product of the corresponding Taylor coefficients.
(defun ht017-tuple-degree (code positions radix)
  (declare (xargs :measure (nfix positions)))
  (if (zp positions)
      0
    (+ (mod code radix)
       (ht017-tuple-degree (floor code radix)
                           (- positions 1)
                           radix))))

(defun ht017-tuple-coefficient-product (code positions radix)
  (declare (xargs :measure (nfix positions)))
  (if (zp positions)
      1
    (* (ht017-cos-plus-i-sin-coefficient (mod code radix))
       (ht017-tuple-coefficient-product (floor code radix)
                                        (- positions 1)
                                        radix))))

(defun ht017-cauchy-coefficient-sum
    (count positions radix target-degree)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (let ((code (- count 1)))
      (+ (if (equal (ht017-tuple-degree code positions radix)
                    target-degree)
             (ht017-tuple-coefficient-product code positions radix)
           0)
         (ht017-cauchy-coefficient-sum code
                                      positions
                                      radix
                                      target-degree)))))

(defun ht017-power-coefficient (power degree)
  (if (and (natp power)
           (natp degree))
      (let* ((radix (+ degree 1))
             (tuple-count (expt radix power)))
        (ht017-cauchy-coefficient-sum tuple-count
                                     power
                                     radix
                                     degree))
    0))

; Substitution of n*z into an entire power series multiplies its coefficient
; of z^degree by n^degree.  Hence this predicate, universally quantified over
; n and degree by its free ACL2 arguments, is bidirectionally equivalent to
; the full-complex De Moivre identity stated above.
(defun hundred-theorems-017-de-moivre-statement (n degree)
  (implies
   (and (natp n)
        (natp degree))
   (equal
    (ht017-power-coefficient n degree)
    (* (expt n degree)
       (ht017-cos-plus-i-sin-coefficient degree)))))

(value-triple :itpeval-statement-checked)
:q
