# YT6-776 aka "Yeti"

<img align="left" height="300" src="./yeti-drawing.png">
This module implements the YT6-776 application-specific curve. The main feature of this curve is that its scalar field equals the base field of the BLS12-381 curve. The estimated security of YT6-776 equals 124-bit, which is around the same as the BLS12 curves.

The name denotes that it was generated using the Cocks-Pinch method for the embedding degree 6. The size of the curve ($log\:q$) is 776 bits. Hence its performance is comparable BW6-761 curve that embeds BLS12-377.

The reason why such a popular curve as BLS12-381 doesn't have an equally known embedding curve lies in the properties of its base field. Namely, its Fq's two-adicity [\[1\]](https://www.cryptologie.net/article/559/whats-two-adicity/) is low (1), which contributes to the embedding curve having proportionally low FFT space, making them unusable with conventional proving systems like Groth'16. The use for the YT6-776 curve is found in the Gemini [\[2\]](https://eprint.iacr.org/2022/420), being an FFT-free, curve-agnostic proving system.

YT6-776 is found using the [`ecfactory`](https://github.com/scipr-lab/ecfactory) library for SageMath. Additional details about the process can be found in the note about Yafa curves [\[3\]](https://eprint.iacr.org/2022/1145.pdf), which was a great inspiration for this work.

## Parameters
Base field: `q` =
```
302876569457825540224058720088493814197684678175517897646382999490010176693949664027430922002605277999717929660119065492046541203055097398745672542166604177101118255582761412697357085679229754433270902868922720449830309670836412672963
```

Scalar field: `r` (same as BLS12-381 Fq) =
```
4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
```

Trace: `t` =
```
556334928175811767685866265168019893274028091673155517508216967661521459911236919644960862098008653606888062617430745
```

Fundamental discriminant: `D` = `-3`

YT6-776 G1 elliptic curve is defined by the following equation:
```
y^2 = x^3 + 93312
```

## References
- \[1\] What's two-adicity? https://www.cryptologie.net/article/559/whats-two-adicity/
- \[2\] Gemini: Elastic SNARKs for Diverse Environments https://eprint.iacr.org/2022/420
- \[3\] YAFA-108/146: Implementing Ed25519-Embedding Cocks-Pinch Curves in Arkworks-rs https://eprint.iacr.org/2022/1145.pdf
