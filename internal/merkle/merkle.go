// Package merkle 实现基于 SHA-256 的 Merkle 树：构建根哈希、生成包含性证明与证明验证。
// 构建策略：每层节点数为奇数且大于 1 时，复制末尾节点与自身配对；单节点层即为根。
// 叶子哈希 = SHA-256(数据块字节)；内部节点哈希 = SHA-256(左子原始字节 || 右子原始字节)。
package merkle

import (
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
)

// HashLen 是 SHA-256 的字节长度。
const HashLen = 32

// Hash 是 32 字节的 SHA-256 摘要。
type Hash [HashLen]byte

// hashLeaf 返回 data 的 SHA-256。
func hashLeaf(data []byte) Hash {
	return sha256.Sum256(data)
}

// hashPair 返回 SHA-256(l || r)（原始字节拼接）。
func hashPair(l, r Hash) Hash {
	var buf [2 * HashLen]byte
	copy(buf[:HashLen], l[:])
	copy(buf[HashLen:], r[:])
	return sha256.Sum256(buf[:])
}

// parseHex 把 64 位十六进制字符串解析为 Hash。
func parseHex(s string) (Hash, error) {
	var h Hash
	b, err := hex.DecodeString(s)
	if err != nil {
		return h, fmt.Errorf("非法十六进制哈希 %q: %w", s, err)
	}
	if len(b) != HashLen {
		return h, fmt.Errorf("哈希长度应为 %d 字节，实际 %d", HashLen, len(b))
	}
	copy(h[:], b)
	return h, nil
}

// Hex 返回小写十六进制表示。
func (h Hash) Hex() string {
	return hex.EncodeToString(h[:])
}

// 证明项的方向标记。
const (
	SideLeft  = "left"  // 兄弟在当前节点左侧
	SideRight = "right" // 兄弟在当前节点右侧
)

// ProofStep 是包含性证明中的一步：兄弟节点哈希与方向。
// Side=left 时验证计算 SHA-256(兄弟 || 当前)；
// Side=right 时验证计算 SHA-256(当前 || 兄弟)。
type ProofStep struct {
	Sibling string `json:"sibling"`
	Side    string `json:"side"`
}

// Proof 是某数据块的包含性证明：叶子哈希、从叶子到根的证明序列与根哈希。
type Proof struct {
	LeafHash string      `json:"leaf_hash"`
	Steps    []ProofStep `json:"steps"`
	Root     string      `json:"root"`
}

// 定义域错误。
var (
	ErrEmptyBlocks     = errors.New("数据块列表不能为空")
	ErrIndexOutOfRange = errors.New("索引越界")
)

// Build 计算 blocks 的 Merkle 根哈希与叶子数量。
// blocks 不能为空。
func Build(blocks []string) (root string, leafCount int, err error) {
	if len(blocks) == 0 {
		return "", 0, ErrEmptyBlocks
	}
	leaves := make([]Hash, len(blocks))
	for i, b := range blocks {
		leaves[i] = hashLeaf([]byte(b))
	}
	return buildRoot(leaves).Hex(), len(blocks), nil
}

// buildRoot 自底向上构建根。每层奇数(>1)复制末尾节点后两两配对；单节点即根。
// 不修改输入切片。
func buildRoot(in []Hash) Hash {
	level := make([]Hash, len(in))
	copy(level, in)
	for len(level) > 1 {
		level = dupOdd(level)
		nxt := make([]Hash, len(level)/2)
		for i := 0; i < len(level); i += 2 {
			nxt[i/2] = hashPair(level[i], level[i+1])
		}
		level = nxt
	}
	return level[0]
}

// dupOdd 在 level 长度为奇数且大于 1 时，返回末尾节点复制后的新切片；
// 长度为偶数或 1 时原样返回。
func dupOdd(level []Hash) []Hash {
	if len(level)%2 == 0 {
		return level
	}
	out := make([]Hash, len(level)+1)
	copy(out, level)
	out[len(level)] = level[len(level)-1]
	return out
}

// MakeProof 生成 blocks[index] 的包含性证明。
// blocks 为空返回 ErrEmptyBlocks；index 越界返回 ErrIndexOutOfRange。
func MakeProof(blocks []string, index int) (Proof, error) {
	if len(blocks) == 0 {
		return Proof{}, ErrEmptyBlocks
	}
	if index < 0 || index >= len(blocks) {
		return Proof{}, fmt.Errorf("%w: %d（共 %d 个数据块）", ErrIndexOutOfRange, index, len(blocks))
	}
	leaves := make([]Hash, len(blocks))
	for i, b := range blocks {
		leaves[i] = hashLeaf([]byte(b))
	}
	level := leaves
	idx := index
	steps := make([]ProofStep, 0, 8)
	for len(level) > 1 {
		level = dupOdd(level)
		var sibIdx int
		var side string
		if idx%2 == 0 {
			sibIdx = idx + 1
			side = SideRight
		} else {
			sibIdx = idx - 1
			side = SideLeft
		}
		steps = append(steps, ProofStep{Sibling: level[sibIdx].Hex(), Side: side})
		nxt := make([]Hash, len(level)/2)
		for i := 0; i < len(level); i += 2 {
			nxt[i/2] = hashPair(level[i], level[i+1])
		}
		level = nxt
		idx /= 2
	}
	return Proof{
		LeafHash: leaves[0].Hex(),
		Steps:    steps,
		Root:     level[0].Hex(),
	}, nil
}

// Verify 校验 leafHashHex 经 steps 是否能重构出 rootHex。
// 空证明 + 根等于叶子哈希时返回 true（单叶子树）。
// 任一哈希不是合法 64 位十六进制、或方向不是 left/right 时返回错误。
func Verify(leafHashHex string, steps []ProofStep, rootHex string) (bool, error) {
	if steps == nil {
		return false, nil
	}
	cur, err := parseHex(leafHashHex)
	if err != nil {
		return false, err
	}
	root, err := parseHex(rootHex)
	if err != nil {
		return false, err
	}
	for i, s := range steps {
		sib, err := parseHex(s.Sibling)
		if err != nil {
			return false, fmt.Errorf("第 %d 步: %w", i, err)
		}
		switch s.Side {
		case SideLeft:
			cur = hashPair(sib, cur)
		case SideRight:
			cur = hashPair(cur, sib)
		default:
			return false, fmt.Errorf("第 %d 步方向非法 %q（应为 left 或 right）", i, s.Side)
		}
	}
	return cur == root, nil
}
