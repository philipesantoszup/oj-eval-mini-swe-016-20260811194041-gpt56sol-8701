#include <algorithm>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

namespace {
constexpr std::size_t PAGE_SIZE = 8192;
constexpr int MAX_KEYS = 111;
constexpr const char *DB_FILE = "bpt.dat";
constexpr char MAGIC[8] = {'B','P','T','0','1','7','\0','\0'};

#pragma pack(push, 1)
struct Key {
    char index[65];
    std::int32_t value;
};
#pragma pack(pop)

struct Node {
    bool leaf = true;
    std::uint16_t count = 0;
    std::uint32_t next = UINT32_MAX;
    Key keys[MAX_KEYS + 2]{};
    std::uint32_t child[MAX_KEYS + 3]{};
};

static_assert(7 + sizeof(Key) * MAX_KEYS + sizeof(std::uint32_t) * (MAX_KEYS + 1) <= PAGE_SIZE,
              "node serialization exceeds page size");

struct Split {
    bool split = false;
    Key separator{};
    std::uint32_t right = 0;
    bool inserted = false;
};

int compareKey(const Key &a, const Key &b) {
    int c = std::strcmp(a.index, b.index);
    if (c != 0) return c < 0 ? -1 : 1;
    if (a.value < b.value) return -1;
    if (a.value > b.value) return 1;
    return 0;
}

Key makeKey(const std::string &index, int value) {
    Key k{};
    std::memcpy(k.index, index.data(), index.size());
    k.index[index.size()] = '\0';
    k.value = value;
    return k;
}

class BPlusTree {
    FILE *file_ = nullptr;
    std::uint32_t root_ = 0;
    std::uint32_t pages_ = 0;
    std::vector<std::unique_ptr<Node>> cache_;
    std::vector<unsigned char> dirty_;

    long offset(std::uint32_t id) const {
        return static_cast<long>((static_cast<std::uint64_t>(id) + 1) * PAGE_SIZE);
    }

    void writeHeader() {
        unsigned char page[PAGE_SIZE]{};
        std::memcpy(page, MAGIC, sizeof(MAGIC));
        std::memcpy(page + 8, &root_, sizeof(root_));
        std::memcpy(page + 12, &pages_, sizeof(pages_));
        std::fseek(file_, 0, SEEK_SET);
        std::fwrite(page, 1, PAGE_SIZE, file_);
    }

    Node readNode(std::uint32_t id) {
        if (cache_[id]) return *cache_[id];

        unsigned char page[PAGE_SIZE]{};
        std::fseek(file_, offset(id), SEEK_SET);
        if (std::fread(page, 1, PAGE_SIZE, file_) != PAGE_SIZE) {
            std::fprintf(stderr, "database read failure\n");
            std::exit(1);
        }
        auto n = std::make_unique<Node>();
        n->leaf = page[0] != 0;
        std::memcpy(&n->count, page + 1, 2);
        std::memcpy(&n->next, page + 3, 4);
        std::memcpy(n->keys, page + 7, sizeof(Key) * MAX_KEYS);
        std::memcpy(n->child, page + 7 + sizeof(Key) * MAX_KEYS,
                    sizeof(std::uint32_t) * (MAX_KEYS + 1));
        Node result = *n;
        cache_[id] = std::move(n);
        return result;
    }

    void writeNode(std::uint32_t id, const Node &n) {
        if (!cache_[id]) cache_[id] = std::make_unique<Node>();
        *cache_[id] = n;
        dirty_[id] = 1;
    }

    void flushNode(std::uint32_t id) {
        if (!dirty_[id]) return;
        const Node &n = *cache_[id];
        unsigned char page[PAGE_SIZE]{};
        page[0] = n.leaf ? 1 : 0;
        std::memcpy(page + 1, &n.count, 2);
        std::memcpy(page + 3, &n.next, 4);
        std::memcpy(page + 7, n.keys, sizeof(Key) * MAX_KEYS);
        std::memcpy(page + 7 + sizeof(Key) * MAX_KEYS, n.child,
                    sizeof(std::uint32_t) * (MAX_KEYS + 1));
        std::fseek(file_, offset(id), SEEK_SET);
        if (std::fwrite(page, 1, PAGE_SIZE, file_) != PAGE_SIZE) {
            std::fprintf(stderr, "database write failure\n");
            std::exit(1);
        }
        dirty_[id] = 0;
    }

    std::uint32_t allocate(const Node &n) {
        std::uint32_t id = pages_++;
        cache_.resize(pages_);
        dirty_.resize(pages_);
        writeNode(id, n);
        return id;
    }

    int lowerBound(const Node &n, const Key &key) const {
        int lo = 0, hi = n.count;
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            if (compareKey(n.keys[mid], key) < 0) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    int upperBound(const Node &n, const Key &key) const {
        int lo = 0, hi = n.count;
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            if (compareKey(key, n.keys[mid]) >= 0) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    std::uint32_t liveCount(std::uint32_t id) {
        Node n = readNode(id);
        return n.leaf ? n.count : n.next;
    }

    Split insertRecursive(std::uint32_t id, const Key &key) {
        Node n = readNode(id);
        if (n.leaf) {
            int pos = lowerBound(n, key);
            if (pos < n.count && compareKey(n.keys[pos], key) == 0) return {};
            for (int i = n.count; i > pos; --i) n.keys[i] = n.keys[i - 1];
            n.keys[pos] = key;
            ++n.count;
            if (n.count <= MAX_KEYS) {
                writeNode(id, n);
                return {false, {}, 0, true};
            }

            Node right;
            right.leaf = true;
            const int leftCount = n.count / 2;
            right.count = n.count - leftCount;
            for (int i = 0; i < right.count; ++i) right.keys[i] = n.keys[leftCount + i];
            n.count = leftCount;
            right.next = n.next;
            std::uint32_t rightId = allocate(right);
            n.next = rightId;
            writeNode(id, n);
            return {true, right.keys[0], rightId, true};
        }

        int branch = upperBound(n, key);
        Split childSplit = insertRecursive(n.child[branch], key);
        if (!childSplit.inserted) return {};
        ++n.next;
        if (!childSplit.split) {
            writeNode(id, n);
            return {false, {}, 0, true};
        }

        for (int i = n.count; i > branch; --i) n.keys[i] = n.keys[i - 1];
        for (int i = n.count + 1; i > branch + 1; --i) n.child[i] = n.child[i - 1];
        n.keys[branch] = childSplit.separator;
        n.child[branch + 1] = childSplit.right;
        ++n.count;
        if (n.count <= MAX_KEYS) {
            writeNode(id, n);
            return {false, {}, 0, true};
        }

        Node right;
        right.leaf = false;
        const int middle = n.count / 2;
        Key promoted = n.keys[middle];
        right.count = n.count - middle - 1;
        for (int i = 0; i < right.count; ++i) right.keys[i] = n.keys[middle + 1 + i];
        for (int i = 0; i <= right.count; ++i) right.child[i] = n.child[middle + 1 + i];
        n.count = middle;
        n.next = 0;
        right.next = 0;
        for (int i = 0; i <= n.count; ++i) n.next += liveCount(n.child[i]);
        for (int i = 0; i <= right.count; ++i) right.next += liveCount(right.child[i]);
        std::uint32_t rightId = allocate(right);
        writeNode(id, n);
        return {true, promoted, rightId, true};
    }

    bool eraseRecursive(std::uint32_t id, const Key &key) {
        Node n = readNode(id);
        if (n.leaf) {
            int pos = lowerBound(n, key);
            if (pos == n.count || compareKey(n.keys[pos], key) != 0) return false;
            for (int i = pos + 1; i < n.count; ++i) n.keys[i - 1] = n.keys[i];
            --n.count;
            writeNode(id, n);
            return true;
        }
        int branch = upperBound(n, key);
        if (!eraseRecursive(n.child[branch], key)) return false;
        --n.next;
        writeNode(id, n);
        return true;
    }

    void findRecursive(std::uint32_t id, const Key &low, const Key &high, bool &any) {
        Node n = readNode(id);
        if (n.leaf) {
            int pos = lowerBound(n, low);
            while (pos < n.count && compareKey(n.keys[pos], high) <= 0) {
                if (any) std::cout << ' ';
                std::cout << n.keys[pos].value;
                any = true;
                ++pos;
            }
            return;
        }
        int branch = upperBound(n, low);
        for (int i = branch; i <= n.count; ++i) {
            if (i > branch && compareKey(n.keys[i - 1], high) > 0) break;
            if (liveCount(n.child[i]) != 0) findRecursive(n.child[i], low, high, any);
        }
    }

    std::uint32_t findLeaf(const Key &key) {
        std::uint32_t id = root_;
        while (true) {
            Node n = readNode(id);
            if (n.leaf) return id;
            id = n.child[upperBound(n, key)];
        }
    }

public:
    BPlusTree() {
        file_ = std::fopen(DB_FILE, "r+b");
        bool valid = false;
        if (file_) {
            unsigned char header[16]{};
            if (std::fread(header, 1, sizeof(header), file_) == sizeof(header) &&
                std::memcmp(header, MAGIC, sizeof(MAGIC)) == 0) {
                std::memcpy(&root_, header + 8, 4);
                std::memcpy(&pages_, header + 12, 4);
                valid = pages_ > 0 && root_ < pages_;
            }
        }
        if (valid) {
            cache_.resize(pages_);
            dirty_.resize(pages_);
        } else {
            if (file_) std::fclose(file_);
            file_ = std::fopen(DB_FILE, "w+b");
            if (!file_) {
                std::fprintf(stderr, "cannot create database\n");
                std::exit(1);
            }
            pages_ = 0;
            cache_.clear();
            dirty_.clear();
            Node root;
            root.leaf = true;
            root_ = allocate(root);
            writeHeader();
        }
    }

    ~BPlusTree() {
        if (file_) {
            for (std::uint32_t id = 0; id < pages_; ++id) flushNode(id);
            writeHeader();
            std::fflush(file_);
            std::fclose(file_);
        }
    }

    void insert(const std::string &index, int value) {
        Key key = makeKey(index, value);
        Split s = insertRecursive(root_, key);
        if (s.split) {
            Node newRoot;
            newRoot.leaf = false;
            newRoot.count = 1;
            newRoot.keys[0] = s.separator;
            newRoot.child[0] = root_;
            newRoot.child[1] = s.right;
            newRoot.next = liveCount(root_) + liveCount(s.right);
            root_ = allocate(newRoot);
        }
    }

    void erase(const std::string &index, int value) {
        eraseRecursive(root_, makeKey(index, value));
    }

    void find(const std::string &index) {
        Key low = makeKey(index, INT_MIN);
        Key high = makeKey(index, INT_MAX);
        bool any = false;
        findRecursive(root_, low, high, any);
        if (!any) std::cout << "null";
        std::cout << '\n';
    }
};
}

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    int n;
    if (!(std::cin >> n)) return 0;
    BPlusTree tree;
    std::string command, index;
    int value;
    while (n--) {
        std::cin >> command >> index;
        if (command == "insert") {
            std::cin >> value;
            tree.insert(index, value);
        } else if (command == "delete") {
            std::cin >> value;
            tree.erase(index, value);
        } else {
            tree.find(index);
        }
    }
    return 0;
}
