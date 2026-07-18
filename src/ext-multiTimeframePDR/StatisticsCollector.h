#ifndef STATISTICS_COLLECTOR_H
#define STATISTICS_COLLECTOR_H

#include <cmath>
#include <limits>
#include <cassert>
#include <map>
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <vector>
#include <queue>

class StatisticsCollector {
private:
    int min_value;
    int max_value;
    size_t sum;
    size_t sum_squares;
    size_t count;
    std::map<int, size_t> frequency;  // Store frequency for mode and median calculation

public:
    StatisticsCollector() : 
        min_value(std::numeric_limits<int>::max()),
        max_value(std::numeric_limits<int>::min()),
        sum(0),
        sum_squares(0),
        count(0)
    {}

    const std::map<int, size_t>& get_frequency() const {
        return frequency;
    }

    // Add a new value to the statistics
    void add(int value) {
        assert(value >= 0 && "Value must be non-negative");

        min_value = std::min(min_value, value);
        max_value = std::max(max_value, value);
        sum += value;
        sum_squares += value * value;
        count++;

        // Update frequency for mode and median calculation
        frequency[value]++;
    }

    // Statistical queries
    int get_min() const {
        assert(count > 0 && "No data points available");
        return min_value;
    }

    int get_max() const {
        assert(count > 0 && "No data points available");
        return max_value;
    }

    double get_mean() const {
        assert(count > 0 && "No data points available");
        return static_cast<double>(sum) / count;
    }

    double get_variance() const {
        assert(count >= 2 && "Need at least 2 data points for variance calculation");
        double mean = get_mean();
        return (sum_squares - count * mean * mean) / (count - 1);
    }

    double get_std_dev() const {
        assert(count >= 2 && "Need at least 2 data points for standard deviation calculation");
        return std::sqrt(get_variance());
    }

    int get_percentile(double ratio) const {
        assert(ratio >= 0.0 && ratio <= 1.0 && "Ratio must be between 0 and 1");
        assert(count > 0 && "No data points available");

        size_t target_index = static_cast<size_t>(std::round(ratio * (count - 1)));
        size_t current_count = 0;

        for (const auto& pair : frequency) {
            current_count += pair.second;
            if (current_count > target_index) {
                return pair.first;
            }
        }

        assert(false && "Failed to calculate median for given ratio");
        return 0;  // Unreachable, but silences compiler warning
    }


    size_t get_count() const {
        return count;
    }

    size_t get_sum() const {
        return sum;
    }

    // Get frequency of a specific value
    size_t get_frequency(int value) const {
        auto it = frequency.find(value);
        return (it != frequency.end()) ? it->second : 0;
    }

    // Reset the collector
    void reset() {
        min_value = std::numeric_limits<int>::max();
        max_value = std::numeric_limits<int>::min();
        sum = 0;
        sum_squares = 0;
        count = 0;
        frequency.clear();
    }

    // Check if we have any data
    bool is_empty() const {
        return count == 0;
    }

    // Print all statistics
    void print_all_statistics() const {
        if (is_empty()) {
            std::cout << "No statistics available (no data points)" << std::endl;
            return;
        }

        // Set up formatting
        std::cout << std::fixed << std::setprecision(2);
        
        // Basic statistics
        std::cout << "=== Statistics Summary ===" << std::endl;
        std::cout << "Count          : " << count << std::endl;
        std::cout << "Minimum        : " << min_value << std::endl;
        std::cout << "Maximum        : " << max_value << std::endl;
        std::cout << "Sum            : " << sum << std::endl;
        std::cout << "Mean           : " << get_mean() << std::endl;
        
        std::cout << "Percentile 50% : " << get_percentile(0.5) << std::endl;
        
        // Advanced statistics (require at least 2 data points)
        if (count >= 2) {
            std::cout << "Variance       : " << get_variance() << std::endl;
            std::cout << "Std Deviation  : " << get_std_dev() << std::endl;
        } else {
            std::cout << "Variance       : N/A (need >= 2 points)" << std::endl;
            std::cout << "Std Deviation  : N/A (need >= 2 points)" << std::endl;
        }
        
        // Frequency distribution
        std::cout << "\nFrequency Distribution:" << std::endl;
        std::cout << "Value  | Frequency | Percentage" << std::endl;
        std::cout << "--------------------------------" << std::endl;
        for (const auto& pair : frequency) {
            double percentage = (100.0 * pair.second) / count;
            std::cout << std::setw(6) << pair.first << " | "
                     << std::setw(9) << pair.second << " | "
                     << std::setw(7) << percentage << "%" << std::endl;
        }
        std::cout << "=======================\n" << std::endl;
    }
};

#endif // STATISTICS_COLLECTOR_H
