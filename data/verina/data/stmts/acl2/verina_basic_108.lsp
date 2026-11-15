;; Statement-only formalization of VERINA corpus artifact verina_basic_108,
;; catalog title "below_zero": construction of integer prefix sums and
;; detection of a negative cumulative value. This file contains no proof.

(in-package "ACL2")

(defun verina-basic-108-integer-listp (xs)
  (if (consp xs)
      (and (integerp (car xs))
           (verina-basic-108-integer-listp (cdr xs)))
    (equal xs nil)))

(defun verina-basic-108-booleanp (value)
  (or (equal value t)
      (equal value nil)))

;; The source precondition is True.
(defun verina-basic-108-below-zero-precond (operations)
  (declare (ignore operations))
  t)

(defun verina-basic-108-last-default-zero (xs)
  (if (consp xs)
      (if (consp (cdr xs))
          (verina-basic-108-last-default-zero (cdr xs))
        (car xs))
    0))

;; This is the source foldl: start from (0), then append the previous last
;; value plus the next operation.
(defun verina-basic-108-build-s-aux (operations accumulator)
  (if (consp operations)
      (let ((next-value
             (+ (verina-basic-108-last-default-zero accumulator)
                (car operations))))
        (verina-basic-108-build-s-aux
         (cdr operations)
         (append accumulator (list next-value))))
    accumulator))

(defun verina-basic-108-build-s (operations)
  (verina-basic-108-build-s-aux operations (list 0)))

(defun verina-basic-108-check-negative (xs)
  (if (consp xs)
      (if (< (car xs) 0)
          t
        (verina-basic-108-check-negative (cdr xs)))
    nil))

;; A cons pair represents the source product (Array Int x Bool); the array is
;; represented extensionally by its finite true list of integer entries.
(defun verina-basic-108-below-zero (operations)
  (let* ((s (verina-basic-108-build-s operations))
         (result (verina-basic-108-check-negative s)))
    (cons s result)))

(defun verina-basic-108-step-recurrencep (operations s)
  (if (consp operations)
      (and (consp s)
           (consp (cdr s))
           (equal (cadr s)
                  (+ (car s) (car operations)))
           (verina-basic-108-step-recurrencep
            (cdr operations) (cdr s)))
    t))

(defun verina-basic-108-any-negativep (xs)
  (if (consp xs)
      (or (< (car xs) 0)
          (verina-basic-108-any-negativep (cdr xs)))
    nil))

(defun verina-basic-108-all-nonnegativep (xs)
  (if (consp xs)
      (and (<= 0 (car xs))
           (verina-basic-108-all-nonnegativep (cdr xs)))
    (equal xs nil)))

(defun verina-basic-108-below-zero-postcond (operations output)
  (let* ((s (car output))
         (result (cdr output)))
    (and
     (verina-basic-108-integer-listp operations)
     (consp output)
     (verina-basic-108-integer-listp s)
     (verina-basic-108-booleanp result)
     (equal (len s) (+ (len operations) 1))
     (consp s)
     (equal (car s) 0)
     (verina-basic-108-step-recurrencep operations s)
     (implies
      (equal result t)
      (verina-basic-108-any-negativep (cdr s)))
     (implies
      (equal result nil)
      (verina-basic-108-all-nonnegativep s)))))

(defun-sk verina-basic-108-below-zero-spec-satisfied-statement ()
  (forall (operations)
    (implies
     (and (verina-basic-108-integer-listp operations)
          (verina-basic-108-below-zero-precond operations))
     (verina-basic-108-below-zero-postcond
      operations
      (verina-basic-108-below-zero operations)))))

(value-triple :itpeval-statement-checked)
:q
