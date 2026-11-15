;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/kmp_KnuthMorrisPratt_kmpqtvc: the Knuth-Morris-Pratt search
;; verification condition for preserving the matching invariant and returning
;; the first occurrence of a pattern. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integers
;; and lists. The abstract source character type is used only through equality,
;; so its elements are represented by arbitrary ACL2 objects.

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

;; Character lookup uses the same Int.toNat conversion. Every occurrence that
;; can affect the verification condition is guarded in range, so ACL2's NIL
;; outside a list does not affect the represented proposition.

(defun ntp4vc-kmp-nth-char (xs index)
  (nth
   (ntp4vc-kmp-int-to-nat index)
   xs))

;; The pointwise clause in matches1 retains its quantifier over all
;; mathematical integer indices.

(defun-sk ntp4vc-kmp-matching-elements-p
    (a1 i1 a2 i2 count)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index count))
      (equal
       (ntp4vc-kmp-nth-char a1 (+ i1 index))
       (ntp4vc-kmp-nth-char a2 (+ i2 index)))))))

(defun ntp4vc-kmp-matches1-p
    (a1 i1 a2 i2 count)
  (and
   (<= 0 i1)
   (<= i1 (- (len a1) count))
   (<= 0 i2)
   (<= i2 (- (len a2) count))
   (ntp4vc-kmp-matching-elements-p
    a1 i1 a2 i2 count)))

(defun-sk ntp4vc-kmp-no-larger-border-p
    (p border j)
  (forall (z)
    (implies
     (integerp z)
     (implies
      (and
       (< border z)
       (< z j))
      (not
       (ntp4vc-kmp-matches1-p
        p (- j z) p 0 z))))))

(defun ntp4vc-kmp-is-next-p (p j border)
  (and
   (<= 0 border)
   (< border j)
   (ntp4vc-kmp-matches1-p
    p (- j border) p 0 border)
   (ntp4vc-kmp-no-larger-border-p
    p border j)))

(defun-sk ntp4vc-kmp-no-earlier-match-p
    (p a upper pattern-length)
  (forall (k)
    (implies
     (integerp k)
     (implies
      (and
       (<= 0 k)
       (< k upper))
      (not
       (ntp4vc-kmp-matches1-p
        a k p 0 pattern-length))))))

(defun ntp4vc-kmp-first-occur-p (p a result)
  (and
   (implies
    (and
     (<= 0 result)
     (< result (len a)))
    (ntp4vc-kmp-matches1-p
     a result p 0 (len p)))
   (ntp4vc-kmp-no-earlier-match-p
    p a result (len p))))

;; This is the complete source condition on an admissible failure table.

(defun-sk ntp4vc-kmp-next-table-p (p next)
  (forall (j)
    (implies
     (integerp j)
     (implies
      (and
       (< 0 j)
       (< j (len p)))
      (ntp4vc-kmp-is-next-p
       p j (ntp4vc-kmp-nth-int next j))))))

(defun ntp4vc-kmp-state-p
    (p a j i m n)
  (and
   (<= 0 j)
   (<= j m)
   (<= j i)
   (<= i n)
   (ntp4vc-kmp-matches1-p
    a (- i j) p 0 j)
   (ntp4vc-kmp-no-earlier-match-p
    p a (- i j) m)))

(defun ntp4vc-kmp-initial-state-p
    (p a m n)
  (and
   (<= 0 0)
   (<= 0 m)
   (<= 0 0)
   (<= 0 n)
   (ntp4vc-kmp-matches1-p
    a (- 0 0) p 0 0)
   (ntp4vc-kmp-no-earlier-match-p
    p a (- 0 0) m)))

;; The successful comparison, zero-border, and failure-table fallback branches
;; retain the source termination disjunctions and complete next-state
;; invariants.

(defun ntp4vc-kmp-successful-comparison-p
    (p a j i m n)
  (and
   (or
    (and
     (<= 0 (- n i))
     (< (- n (+ i 1)) (- n i)))
    (and
     (equal (- n i) (- n (+ i 1)))
     (<= 0 j)
     (< (+ j 1) j)))
   (ntp4vc-kmp-state-p
    p a (+ j 1) (+ i 1) m n)))

(defun ntp4vc-kmp-zero-border-p
    (p a j i m n)
  (and
   (or
    (and
     (<= 0 (- n i))
     (< (- n (+ i 1)) (- n i)))
    (and
     (equal (- n i) (- n (+ i 1)))
     (<= 0 j)
     (< j j)))
   (ntp4vc-kmp-state-p
    p a j (+ i 1) m n)))

(defun ntp4vc-kmp-fallback-p
    (p a next j i m n)
  (let ((new-j
         (ntp4vc-kmp-nth-int next j)))
    (and
     (<= 0 j)
     (< j (len next))
     (or
      (and
       (<= 0 (- n i))
       (< (- n i) (- n i)))
      (and
       (<= 0 j)
       (< new-j j)))
     (ntp4vc-kmp-state-p
      p a new-j i m n))))

(defun ntp4vc-kmp-comparison-branch-p
    (p a next j i m n)
  (and
   (<= 0 j)
   (< j (len p))
   (<= 0 i)
   (< i (len a))
   (if
       (equal
        (ntp4vc-kmp-nth-char a i)
        (ntp4vc-kmp-nth-char p j))
       (ntp4vc-kmp-successful-comparison-p
        p a j i m n)
     (if (equal j 0)
         (ntp4vc-kmp-zero-border-p
          p a j i m n)
       (ntp4vc-kmp-fallback-p
        p a next j i m n)))))

;; When the loop guard is false, every integer result satisfying the source
;; conditional assignment must satisfy first_occur.

(defun-sk ntp4vc-kmp-result-continuation-p
    (p a j i m)
  (forall (result)
    (implies
     (integerp result)
     (implies
      (equal
       result
       (if (equal j m)
           (- i m)
         i))
      (ntp4vc-kmp-first-occur-p
       p a result)))))

(defun ntp4vc-kmp-guard-result-p
    (p a next j i m n guard)
  (if (equal guard t)
      (ntp4vc-kmp-comparison-branch-p
       p a next j i m n)
    (ntp4vc-kmp-result-continuation-p
     p a j i m)))

;; Source Bool is represented exactly by ACL2's two Boolean values. The
;; defining condition on o1 and its implication retain their original scope.

(defun-sk ntp4vc-kmp-guard-continuation-p
    (p a next j i m n)
  (forall (guard)
    (implies
     (booleanp guard)
     (implies
      (equal
       guard
       (if (< j m)
           (if (< i n) t nil)
         nil))
      (ntp4vc-kmp-guard-result-p
       p a next j i m n guard)))))

(defun-sk ntp4vc-kmp-all-loop-states-p
    (p a next m n)
  (forall (j i)
    (implies
     (and
      (integerp j)
      (integerp i))
     (implies
      (ntp4vc-kmp-state-p
       p a j i m n)
      (ntp4vc-kmp-guard-continuation-p
       p a next j i m n)))))

(defun ntp4vc-kmp-next-conclusion-p
    (p a next m n)
  (and
   (ntp4vc-kmp-initial-state-p
    p a m n)
   (ntp4vc-kmp-all-loop-states-p
    p a next m n)))

;; The source theorem universally quantifies next over all integer lists.

(defun-sk ntp4vc-kmp-all-next-lists-p
    (p a m n)
  (forall (next)
    (implies
     (ntp4vc-kmp-integer-list-p next)
     (implies
      (and
       (equal (len next) (len p))
       (ntp4vc-kmp-next-table-p p next))
      (ntp4vc-kmp-next-conclusion-p
       p a next m n)))))

(defun
    ntp4vc-pearl-kmp-knuthmorrispratt-kmpqtvc-statement
    (p a)
  (implies
   (and
    (true-listp p)
    (true-listp a)
    (<= 1 (len p)))
   (let ((m (len p))
         (n (len a)))
     (and
      (<= 1 (len p))
      (ntp4vc-kmp-all-next-lists-p
       p a m n)))))

(value-triple :itpeval-statement-checked)
:q
