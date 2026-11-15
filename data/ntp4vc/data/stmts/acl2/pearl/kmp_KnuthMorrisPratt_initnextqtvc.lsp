;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/kmp_KnuthMorrisPratt_initnextqtvc: the verification condition for
;; initializing and maintaining the Knuth-Morris-Pratt failure table.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integers
;; and lists.  The source character type is used only through equality, so its
;; elements are represented by arbitrary ACL2 objects.

(defun ntp4vc-kmp-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (ntp4vc-kmp-integer-list-p (cdr xs)))))

(defun ntp4vc-kmp-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

;; Source integer-list lookup uses Int.toNat and has default value zero.

(defun ntp4vc-kmp-nth-int (xs index)
  (let ((value
         (nth
          (ntp4vc-kmp-int-to-nat index)
          xs)))
    (if (integerp value)
        value
      0)))

;; Character lookup uses the same Int.toNat conversion.  Every occurrence in
;; the verification condition is guarded in range, so ACL2's NIL outside a
;; list does not affect the represented proposition.

(defun ntp4vc-kmp-nth-char (xs index)
  (nth
   (ntp4vc-kmp-int-to-nat index)
   xs))

;; List.set changes an in-range natural position and otherwise leaves the
;; finite list unchanged.

(defun ntp4vc-kmp-list-set (xs index value)
  (if (< (ntp4vc-kmp-int-to-nat index) (len xs))
      (update-nth
       (ntp4vc-kmp-int-to-nat index)
       value
       xs)
    xs))

;; The pointwise clause in matches1 retains its source-wide integer
;; quantifier.

(defun-sk ntp4vc-kmp-matching-elements-p
    (a1 i1 a2 i2 n)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index n))
      (equal
       (ntp4vc-kmp-nth-char a1 (+ i1 index))
       (ntp4vc-kmp-nth-char a2 (+ i2 index)))))))

(defun ntp4vc-kmp-matches1-p
    (a1 i1 a2 i2 n)
  (and
   (<= 0 i1)
   (<= i1 (- (len a1) n))
   (<= 0 i2)
   (<= i2 (- (len a2) n))
   (ntp4vc-kmp-matching-elements-p
    a1 i1 a2 i2 n)))

(defun-sk ntp4vc-kmp-no-larger-border-p
    (p lower upper total)
  (forall (z)
    (implies
     (integerp z)
     (implies
      (and
       (< lower z)
       (< z upper))
      (not
       (ntp4vc-kmp-matches1-p
        p (- total z) p 0 z))))))

(defun ntp4vc-kmp-is-next-p (p j n)
  (and
   (<= 0 n)
   (< n j)
   (ntp4vc-kmp-matches1-p
    p (- j n) p 0 n)
   (ntp4vc-kmp-no-larger-border-p
    p n j j)))

;; This is the source equality between integer-indexed lookup functions,
;; represented extensionally over every mathematical integer argument.

(defun-sk ntp4vc-kmp-update-function-equality-p
    (updated original index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (ntp4vc-kmp-nth-int updated argument)
      (if (equal argument index)
          value
        (ntp4vc-kmp-nth-int original argument))))))

(defun-sk ntp4vc-kmp-zero-initialized-p
    (xs bound)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index bound))
      (equal
       (ntp4vc-kmp-nth-int xs index)
       0)))))

(defun-sk ntp4vc-kmp-next-through-p
    (p xs upper)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (< 0 k)
       (<= k upper))
      (ntp4vc-kmp-is-next-p
       p k (ntp4vc-kmp-nth-int xs k))))))

(defun-sk ntp4vc-kmp-next-before-length-p
    (p xs)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and
       (< 0 j)
       (< j (len p)))
      (ntp4vc-kmp-is-next-p
       p j (ntp4vc-kmp-nth-int xs j))))))

(defun ntp4vc-kmp-final-table-p (p xs)
  (and
   (equal (len xs) (len p))
   (ntp4vc-kmp-next-before-length-p p xs)))

(defun ntp4vc-kmp-loop-invariant-p
    (p m j i xs)
  (and
   (<= 0 j)
   (< j i)
   (<= i m)
   (ntp4vc-kmp-matches1-p
    p (- i j) p 0 j)
   (ntp4vc-kmp-no-larger-border-p
    p (+ j 1) (+ i 1) (+ i 1))
   (ntp4vc-kmp-next-through-p p xs i)))

;; The successful-character branch updates next1[i+1] to j+1.

(defun ntp4vc-kmp-equal-character-conclusion-p
    (p m j i updated)
  (and
   (or
    (and
     (<= 0 (- m i))
     (< (- m (+ i 1)) (- m i)))
    (and
     (equal (- m i) (- m (+ i 1)))
     (<= 0 j)
     (< (+ j 1) j)))
   (<= 0 (+ j 1))
   (< (+ j 1) (+ i 1))
   (<= (+ i 1) m)
   (ntp4vc-kmp-matches1-p
    p
    (- (+ i 1) (+ j 1))
    p
    0
    (+ j 1))
   (ntp4vc-kmp-no-larger-border-p
    p
    (+ j 2)
    (+ i 2)
    (+ i 2))
   (ntp4vc-kmp-next-through-p
    p updated (+ i 1))))

(defun ntp4vc-kmp-equal-character-update-p
    (p m j i xs)
  (let ((updated
         (ntp4vc-kmp-list-set
          xs (+ i 1) (+ j 1))))
    (and
     (<= 0 (+ i 1))
     (< (+ i 1) (len xs))
     (implies
      (equal (len updated) (len xs))
      (implies
       (ntp4vc-kmp-update-function-equality-p
        updated xs (+ i 1) (+ j 1))
       (ntp4vc-kmp-equal-character-conclusion-p
        p m j i updated))))))

;; The zero-border branch updates next1[i+1] to zero.

(defun ntp4vc-kmp-zero-border-conclusion-p
    (p m j i updated)
  (and
   (or
    (and
     (<= 0 (- m i))
     (< (- m (+ i 1)) (- m i)))
    (and
     (equal (- m i) (- m (+ i 1)))
     (<= 0 j)
     (< j j)))
   (<= 0 j)
   (< j (+ i 1))
   (<= (+ i 1) m)
   (ntp4vc-kmp-matches1-p
    p (- (+ i 1) j) p 0 j)
   (ntp4vc-kmp-no-larger-border-p
    p
    (+ j 1)
    (+ i 2)
    (+ i 2))
   (ntp4vc-kmp-next-through-p
    p updated (+ i 1))))

(defun ntp4vc-kmp-zero-border-update-p
    (p m j i xs)
  (let ((updated
         (ntp4vc-kmp-list-set xs (+ i 1) 0)))
    (and
     (<= 0 (+ i 1))
     (< (+ i 1) (len xs))
     (implies
      (equal (len updated) (len xs))
      (implies
       (ntp4vc-kmp-update-function-equality-p
        updated xs (+ i 1) 0)
       (ntp4vc-kmp-zero-border-conclusion-p
        p m j i updated))))))

;; The fallback branch replaces j by next1[j].

(defun ntp4vc-kmp-fallback-p
    (p m j i xs)
  (let ((new-j (ntp4vc-kmp-nth-int xs j)))
    (and
     (<= 0 j)
     (< j (len xs))
     (or
      (and
       (<= 0 (- m i))
       (< (- m i) (- m i)))
      (and
       (<= 0 j)
       (< new-j j)))
     (<= 0 new-j)
     (< new-j i)
     (<= i m)
     (ntp4vc-kmp-matches1-p
      p (- i new-j) p 0 new-j)
     (ntp4vc-kmp-no-larger-border-p
      p
      (+ new-j 1)
      (+ i 1)
      (+ i 1))
     (ntp4vc-kmp-next-through-p p xs i))))

(defun ntp4vc-kmp-loop-step-p
    (p m j i xs)
  (if (< i (- m 1))
      (and
       (<= 0 j)
       (< j (len p))
       (<= 0 i)
       (< i (len p))
       (if
           (equal
            (ntp4vc-kmp-nth-char p i)
            (ntp4vc-kmp-nth-char p j))
           (ntp4vc-kmp-equal-character-update-p
            p m j i xs)
         (if (equal j 0)
             (ntp4vc-kmp-zero-border-update-p
              p m j i xs)
           (ntp4vc-kmp-fallback-p
            p m j i xs))))
    (ntp4vc-kmp-final-table-p p xs)))

;; This retains the source quantifier over every integer pair j,i and every
;; integer list next1 satisfying the loop-state premises.

(defun-sk ntp4vc-kmp-all-loop-states-p
    (p m initialized)
  (forall (j i xs)
    (implies
     (and
      (integerp j)
      (integerp i)
      (ntp4vc-kmp-integer-list-p xs))
     (implies
      (equal (len xs) (len initialized))
      (implies
       (ntp4vc-kmp-loop-invariant-p
        p m j i xs)
       (ntp4vc-kmp-loop-step-p
        p m j i xs))))))

(defun ntp4vc-kmp-initialized-conclusion-p
    (p m initialized)
  (and
   (<= 0 0)
   (< 0 1)
   (<= 1 m)
   (ntp4vc-kmp-matches1-p p 1 p 0 0)
   (ntp4vc-kmp-no-larger-border-p p 1 2 2)
   (ntp4vc-kmp-next-through-p p initialized 1)
   (ntp4vc-kmp-all-loop-states-p
    p m initialized)))

(defun ntp4vc-kmp-nontrivial-initialization-p
    (p m xs)
  (let ((initialized
         (ntp4vc-kmp-list-set xs 1 0)))
    (and
     (<= 0 1)
     (< 1 (len xs))
     (implies
      (equal (len initialized) (len xs))
      (implies
       (ntp4vc-kmp-update-function-equality-p
        initialized xs 1 0)
       (ntp4vc-kmp-initialized-conclusion-p
        p m initialized))))))

(defun ntp4vc-kmp-next-case-p (p m xs)
  (if (< 1 m)
      (ntp4vc-kmp-nontrivial-initialization-p
       p m xs)
    (ntp4vc-kmp-final-table-p p xs)))

;; The source theorem universally quantifies next over integer lists.

(defun-sk ntp4vc-kmp-all-initial-lists-p (p m)
  (forall (xs)
    (implies
     (ntp4vc-kmp-integer-list-p xs)
     (implies
      (and
       (ntp4vc-kmp-zero-initialized-p xs m)
       (equal (len xs) m))
      (ntp4vc-kmp-next-case-p p m xs)))))

(defun ntp4vc-pearl-kmp-knuthmorrispratt-initnextqtvc-statement
    (p)
  (implies
   (and
    (true-listp p)
    (<= 1 (len p)))
   (let ((m (len p)))
     (and
      (<= 0 m)
      (ntp4vc-kmp-all-initial-lists-p p m)))))

(value-triple :itpeval-statement-checked)
:q
