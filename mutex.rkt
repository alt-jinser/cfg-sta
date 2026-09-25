#lang racket
(require redex
         redex/pict
         pict
         racket/draw)

;; Formal syntax definition
(define-language Mutex-Lang
  [S uninitialized unlocked held error]
  [E create
     lock-call
     lock-acquire
     try-lock-call
     try-lock-success
     try-lock-fail
     guard-drop]
  [Trace (E ...)]
  [Config (S Trace)])

;; Small-step operational semantics
(define R
  (reduction-relation Mutex-Lang
    #:domain Config

    ;; Valid transitions
    [--> (uninitialized (create           E ...)) (unlocked (E ...)) "create"]
    [--> (unlocked      (lock-acquire     E ...)) (held     (E ...)) "lock-acquire"]
    [--> (unlocked      (try-lock-success E ...)) (held     (E ...)) "try-lock-success"]
    [--> (unlocked      (try-lock-fail    E ...)) (unlocked (E ...)) "try-lock-fail"]
    [--> (held          (guard-drop       E ...)) (unlocked (E ...)) "guard-drop"]

    ;; State-preserving transitions
    [--> (unlocked      (lock-call        E ...)) (unlocked (E ...)) "st-unlocked-lock-call"]
    [--> (unlocked      (try-lock-call    E ...)) (unlocked (E ...)) "st-unlocked-try-call"]
    [--> (held          (lock-call        E ...)) (held     (E ...)) "st-held-lock-call"]
    [--> (held          (try-lock-call    E ...)) (held     (E ...)) "st-held-try-call"]
    [--> (held          (try-lock-fail    E ...)) (held     (E ...)) "st-held-try-fail"]

    ;; Invalid transitions -> error
    [--> (uninitialized (lock-call        E ...)) (error (E ...)) "err-uninit-lock-call"]
    [--> (uninitialized (try-lock-call    E ...)) (error (E ...)) "err-uninit-try-call"]
    [--> (uninitialized (try-lock-fail    E ...)) (error (E ...)) "err-uninit-try-fail"]
    [--> (uninitialized (lock-acquire     E ...)) (error (E ...)) "err-uninit-acquire"]
    [--> (uninitialized (try-lock-success E ...)) (error (E ...)) "err-uninit-try-success"]
    [--> (uninitialized (guard-drop       E ...)) (error (E ...)) "err-uninit-drop"]
    [--> (unlocked      (guard-drop       E ...)) (error (E ...)) "err-unlocked-drop"]
    [--> (unlocked      (create           E ...)) (error (E ...)) "err-unlocked-create"]
    [--> (held          (create           E ...)) (error (E ...)) "err-held-create"]
    [--> (held          (lock-acquire     E ...)) (error (E ...)) "err-held-acquire"]
    [--> (held          (try-lock-success E ...)) (error (E ...)) "err-held-try-success"]

    ;; Error sink
    [--> (error         (E_head           E ...)) (error (E ...)) "err-sink"]))

;; Trace evaluation
(define-metafunction Mutex-Lang
  eval-config : Config -> S
  [(eval-config (S ())) S]
  [(eval-config Config_1)
   (eval-config Config_2)
   (where (Config_2 _ ...) ,(apply-reduction-relation R (term Config_1)))])

(define (run trace-list)
  (term (eval-config (uninitialized ,trace-list))))

(define (accepts? trace-list)
  (not (eq? (run trace-list) 'error)))

;; Render reduction rules to PNG
(define (save-reduction-relation-png rel filename)
  (define p (reduction-relation->pict rel))
  (define bmp (make-bitmap (exact-ceiling (pict-width p))
                           (exact-ceiling (pict-height p))))
  (define dc (make-object bitmap-dc% bmp))
  (send dc set-smoothing 'aligned)
  (draw-pict p dc 0 0)
  (send bmp save-file filename 'png))

(module+ test
  (require rackunit)

  (check-equal? (run '(create)) 'unlocked)
  (check-equal? (run '(create lock-acquire guard-drop)) 'unlocked)
  (check-equal? (run '(create guard-drop)) 'error)
  (check-true  (accepts? '(create lock-acquire guard-drop)))
  (check-false (accepts? '(create guard-drop)))

  ;; Property: Error is an absorbing state
  (check-true
   (redex-check Mutex-Lang
                (E Trace)
                (eq? (term (eval-config (error (E . Trace)))) 'error))))

(module+ main
  (save-reduction-relation-png R "mutex-semantics.png")
  (render-reduction-relation R "mutex-semantics.tex")
  (traces R (term (uninitialized (create lock-acquire guard-drop)))))
