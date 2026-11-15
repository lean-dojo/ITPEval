;; Statement-only formalization of VERINA corpus artifact verina_advanced_22,
;; "isPeakValley": a deterministic scan decides whether an integer list
;; strictly increases and then strictly decreases, with both phases nonempty,
;; together with its finite-index Boolean correctness contract. This file
;; contains no proof.

(in-package "ACL2")

(defun verina-advanced-22-integer-listp (lst)
  (if (consp lst)
      (and
       (integerp (car lst))
       (verina-advanced-22-integer-listp (cdr lst)))
    (equal lst nil)))

(defun verina-advanced-22-is-peak-valley-precond (lst)
  (declare (ignore lst))
  t)

;; This is the source's one-pass local aux recursion. The two Boolean flags
;; record whether an increase has occurred and whether descent has started.

(defun verina-advanced-22-aux
    (lst increasing started-decreasing)
  (declare (xargs :measure (len lst)))
  (if (and
       (consp lst)
       (consp (cdr lst)))
      (let ((x (car lst))
            (y (car (cdr lst))))
        (if (< x y)
            (if started-decreasing
                nil
              (verina-advanced-22-aux
               (cdr lst)
               t
               started-decreasing))
          (if (> x y)
              (if increasing
                  (verina-advanced-22-aux
                   (cdr lst)
                   increasing
                   t)
                nil)
            nil)))
    (and increasing started-decreasing)))

(defun verina-advanced-22-is-peak-valley (lst)
  (verina-advanced-22-aux lst nil nil))

;; Lean's Nat subtraction truncates at zero.

(defun verina-advanced-22-nat-sub (a b)
  (if (and (natp a) (natp b))
      (nfix (- a b))
    0))

;; List.get! on List Int returns the default integer 0 out of bounds.

(defun verina-advanced-22-nth-default-zero (index lst)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp lst)
        (if (zp index)
            (car lst)
          (verina-advanced-22-nth-default-zero
           (- index 1)
           (cdr lst)))
      0)))

;; These two folds are the source postcondition's List.range/all checks.

(defun verina-advanced-22-all-increasing-before
    (index remaining lst)
  (declare (xargs :measure (nfix remaining)))
  (if (not (and (natp index) (natp remaining)))
      nil
    (if (zp remaining)
        t
      (and
       (<
        (verina-advanced-22-nth-default-zero index lst)
        (verina-advanced-22-nth-default-zero
         (+ index 1)
         lst))
       (verina-advanced-22-all-increasing-before
        (+ index 1)
        (- remaining 1)
        lst)))))

(defun verina-advanced-22-all-decreasing-after
    (peak offset remaining lst)
  (declare (xargs :measure (nfix remaining)))
  (if (not (and
            (natp peak)
            (natp offset)
            (natp remaining)))
      nil
    (if (zp remaining)
        t
      (and
       (>
        (verina-advanced-22-nth-default-zero
         (+ peak offset)
         lst)
        (verina-advanced-22-nth-default-zero
         (+ peak offset 1)
         lst))
       (verina-advanced-22-all-decreasing-after
        peak
        (+ offset 1)
        (- remaining 1)
        lst)))))

(defun verina-advanced-22-valid-peak-p (peak lst)
  (let* ((length (len lst))
         (last-index
          (verina-advanced-22-nat-sub length 1))
         (suffix-comparisons
          (verina-advanced-22-nat-sub last-index peak)))
    (and
     (natp peak)
     (<= 1 peak)
     (< peak last-index)
     (verina-advanced-22-all-increasing-before
      0 peak lst)
     (verina-advanced-22-all-decreasing-after
      peak 0 suffix-comparisons lst))))

;; This constructs List.range length filtered by valid-peak-p, in the same
;; increasing index order as the Lean postcondition.

(defun verina-advanced-22-valid-peaks-from
    (peak remaining lst)
  (declare (xargs :measure (nfix remaining)))
  (if (not (and (natp peak) (natp remaining)))
      nil
    (if (zp remaining)
        nil
      (if (verina-advanced-22-valid-peak-p peak lst)
          (cons
           peak
           (verina-advanced-22-valid-peaks-from
            (+ peak 1)
            (- remaining 1)
            lst))
        (verina-advanced-22-valid-peaks-from
         (+ peak 1)
         (- remaining 1)
         lst)))))

(defun verina-advanced-22-valid-peaks (lst)
  (verina-advanced-22-valid-peaks-from
   0
   (len lst)
   lst))

(defun verina-advanced-22-bool-p (result)
  (or (equal result t)
      (equal result nil)))

(defun verina-advanced-22-is-peak-valley-postcond
    (lst result)
  (let ((valid-peaks
         (verina-advanced-22-valid-peaks lst)))
    (and
     (verina-advanced-22-integer-listp lst)
     (verina-advanced-22-bool-p result)
     (implies
      (not (equal valid-peaks nil))
      result)
     (implies
      (equal (len valid-peaks) 0)
      (not result)))))

(defun
    verina-advanced-22-is-peak-valley-spec-satisfied-statement
    (lst)
  (implies
   (and
    (verina-advanced-22-integer-listp lst)
    (verina-advanced-22-is-peak-valley-precond lst))
   (verina-advanced-22-is-peak-valley-postcond
    lst
    (verina-advanced-22-is-peak-valley lst))))

(value-triple :itpeval-statement-checked)
:q
